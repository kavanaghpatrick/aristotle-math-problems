#!/usr/bin/env python3
"""Stage 2 — Analogy Mining.

Calls Grok + Gemini + Codex in parallel (via scripts/debate.py harness) with
the analogy-mining prompt. Consolidates returned JSON arrays into a top-5
ranked analog list.

Usage:
    python3 -m research_fusion.stage2_analogy --problem-id erdos_938
    python3 -m research_fusion.stage2_analogy \\
        --problem-id erdos_938 --models grok,gemini,codex --rounds 1
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

THIS_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = THIS_DIR.parent
RUNS_DIR = THIS_DIR / "runs"
PROMPT_PATH = THIS_DIR / "prompts" / "stage2_analogy.md"
DEBATE_SCRIPT = PROJECT_ROOT / "scripts" / "debate.py"
CACHE_TTL = 7 * 24 * 60 * 60


def _cache_dir(problem_id: str) -> Path:
    d = RUNS_DIR / problem_id / ".cache"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _cache_key(prompt: str, models: list[str]) -> str:
    raw = "|".join(["stage2", ",".join(sorted(models)), prompt])
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def _cache_get(problem_id: str, key: str) -> str | None:
    p = _cache_dir(problem_id) / f"{key}.md"
    if not p.exists():
        return None
    if time.time() - p.stat().st_mtime > CACHE_TTL:
        return None
    return p.read_text()


def _cache_put(problem_id: str, key: str, payload: str) -> None:
    p = _cache_dir(problem_id) / f"{key}.md"
    p.write_text(payload)


# ─────────────────────────────────────────────────────────────────────────
# Prompt assembly
# ─────────────────────────────────────────────────────────────────────────

def build_prompt(card: dict, literature_md: str) -> str:
    template = PROMPT_PATH.read_text()
    # Literature block — keep it tight (~6k chars max).
    snippet = literature_md[:6000]
    english_abstract = card.get("what_is_known", "")
    # Use simple string-replace (NOT .format) because the prompt contains
    # literal JSON `{...}` examples that confuse `.format`.
    substitutions = {
        "{problem_id}": str(card.get("problem_id", "unknown")),
        "{bare_statement}": str(card.get("bare_statement", "(none)")),
        "{english_abstract}":
            str(english_abstract or "(no English gloss available)"),
        "{home_domain}": str(card.get("domain", "nt")),
        "{literature_block}": snippet,
        # Per-model substitution happens inside debate.py at the model layer,
        # so we leave the {model_name} marker intact for the orchestrator.
    }
    out = template
    for k, v in substitutions.items():
        out = out.replace(k, v)
    return out


# ─────────────────────────────────────────────────────────────────────────
# debate.py invocation
# ─────────────────────────────────────────────────────────────────────────

def _build_round_instructions(prompt: str) -> dict[int, str]:
    """One-round debate where the entire prompt IS the instruction."""
    return {1: prompt}


def call_debate(
    problem_id: str,
    card: dict,
    literature_md: str,
    models: list[str],
    rounds: int,
    timeout: int,
    force: bool,
) -> str:
    """Invoke scripts/debate.py with the Stage-2 prompt. Returns markdown text."""
    base_prompt = build_prompt(card, literature_md)
    cache_key = _cache_key(base_prompt, models)
    if not force:
        hit = _cache_get(problem_id, cache_key)
        if hit:
            return hit

    pdir = RUNS_DIR / problem_id
    pdir.mkdir(parents=True, exist_ok=True)
    # debate.py wants a context-file. We pass the literature.md.
    lit_file = pdir / "01_literature.md"
    if not lit_file.exists():
        raise SystemExit(
            f"[stage2] Stage 1 has not been run for {problem_id}. "
            f"Expected: {lit_file}"
        )
    out_file = pdir / "02_analogies_debate.md"
    inst_file: Path | None = None
    try:
        inst = _build_round_instructions(base_prompt)
        inst_file_obj = tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False, dir=str(pdir / ".cache"),
        )
        inst_file = Path(inst_file_obj.name)
        json.dump({str(k): v for k, v in inst.items()}, inst_file_obj)
        inst_file_obj.close()

        topic = (
            f"Analogy mining for {problem_id}: "
            "find structurally similar open or closed problems in OTHER "
            "mathematical areas and the named techniques that unlocked them."
        )
        cmd = [
            "python3", str(DEBATE_SCRIPT),
            "--context", str(lit_file),
            "--topic", topic,
            "--rounds", str(rounds),
            "--output", str(out_file),
            "--models", ",".join(models),
            "--timeout", str(timeout),
            "--round-instructions", str(inst_file),
        ]
        print(f"[stage2] running: {' '.join(cmd)}", file=sys.stderr)
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout * rounds * len(models) + 60)
        if proc.returncode != 0:
            print(f"[stage2] debate.py failed (rc={proc.returncode}): "
                  f"{proc.stderr[:600]}", file=sys.stderr)
            # Still produce a marker file so downstream can detect failure.
            transcript = (
                f"# Stage 2 — debate.py FAILED\n\n"
                f"rc={proc.returncode}\n\n"
                f"```\n{proc.stderr[:2000]}\n```\n"
            )
        else:
            transcript = out_file.read_text() if out_file.exists() else (
                "# Stage 2 — empty transcript (debate.py succeeded but "
                "produced no output)\n"
            )
        _cache_put(problem_id, cache_key, transcript)
        return transcript
    finally:
        if inst_file and inst_file.exists():
            try:
                inst_file.unlink()
            except OSError:
                pass


# ─────────────────────────────────────────────────────────────────────────
# Parse model responses
# ─────────────────────────────────────────────────────────────────────────

def _extract_json_blocks(text: str) -> list[list[dict]]:
    """Greedily pull every json-fence array from the transcript."""
    blocks: list[list[dict]] = []
    for m in re.finditer(r"```json\s*(\[[\s\S]*?\])\s*```", text):
        try:
            arr = json.loads(m.group(1))
        except json.JSONDecodeError:
            continue
        if isinstance(arr, list):
            blocks.append([x for x in arr if isinstance(x, dict)])
    return blocks


def _per_model_blocks(transcript: str) -> dict[str, list[list[dict]]]:
    """Split transcript into per-model sections; extract JSON arrays."""
    # debate.py marks each model's contribution with a `### <name>` heading.
    sections = re.split(r"\n###\s+", transcript)
    out: dict[str, list[list[dict]]] = {}
    for s in sections[1:]:
        # First line is the model display name.
        first_nl = s.find("\n")
        if first_nl < 0:
            continue
        name = s[:first_nl].strip().lower()
        body = s[first_nl + 1:]
        blocks = _extract_json_blocks(body)
        out.setdefault(name, []).extend(blocks)
    return out


def consolidate(transcript: str, home_domain: str) -> list[dict]:
    """Build a top-N consolidated analog list (deduped + ranked)."""
    per_model = _per_model_blocks(transcript)
    pool: dict[str, dict] = {}
    for model_name, blocks in per_model.items():
        for arr in blocks:
            for item in arr:
                if not isinstance(item, dict):
                    continue
                # Required keys
                ap = (item.get("analog_problem") or "").strip()
                if not ap:
                    continue
                # Reject same-home-domain analogs.
                ad = (item.get("analog_domain") or "").strip().lower()
                if ad == home_domain.lower():
                    continue
                # Canonical key (lowercased title) — duplicates fold.
                k = re.sub(r"\W+", "_", ap.lower())[:80]
                if k in pool:
                    pool[k]["supporters"].add(model_name)
                    pool[k]["confidence_sum"] += int(item.get("confidence", 3))
                    pool[k]["confidence_n"] += 1
                else:
                    pool[k] = {
                        "analog_id": item.get("analog_id") or f"A_{len(pool)+1}",
                        "analog_problem": ap,
                        "analog_domain": ad or "unknown",
                        "named_technique": item.get("named_technique", ""),
                        "structural_map": item.get("structural_map", ""),
                        "obstruction": item.get("obstruction", ""),
                        "confidence_sum": int(item.get("confidence", 3)),
                        "confidence_n": 1,
                        "supporters": {model_name},
                    }
    # Rank: supporter count desc, then mean confidence desc.
    ranked = sorted(
        pool.values(),
        key=lambda x: (
            -len(x["supporters"]),
            -(x["confidence_sum"] / max(1, x["confidence_n"])),
        ),
    )
    out = []
    for i, p in enumerate(ranked[:10], 1):
        mean = p["confidence_sum"] / max(1, p["confidence_n"])
        out.append({
            "analog_id": f"A{i}",
            "analog_problem": p["analog_problem"],
            "analog_domain": p["analog_domain"],
            "named_technique": p["named_technique"],
            "structural_map": p["structural_map"],
            "obstruction": p["obstruction"],
            "confidence": int(round(mean)),
            "supporters": sorted(p["supporters"]),
        })
    return out


def render_markdown(
    problem_id: str,
    card: dict,
    transcript: str,
    top_analogs: list[dict],
    models: list[str],
) -> str:
    lines: list[str] = []
    lines.append(f"# Analogy mining — {problem_id}")
    lines.append(
        f"Stage: 2  Models consulted: {', '.join(models)}  "
        f"Generated: {datetime.utcnow().strftime('%Y-%m-%d')}"
    )
    lines.append("")
    lines.append("## Top 5 analogies (consensus, ranked by supporter count + confidence)")
    if not top_analogs:
        lines.append(
            "_No structural analogies were surfaced. Empty result is a valid "
            "Stage-2 outcome — this problem may not have an honest cross-domain "
            "analog within the consulted models' surfaces._"
        )
    for a in top_analogs[:5]:
        lines.append(
            f"### {a['analog_id']}. {a['analog_problem']} — "
            f"{a['named_technique']}"
        )
        lines.append(
            f"- Confidence: {a['confidence']}/5 "
            f"({len(a['supporters'])} of {len(models)} models)"
        )
        lines.append(f"- Home domain: {a['analog_domain']}")
        lines.append(f"- Structural map: {a['structural_map']}")
        lines.append(f"- Obstruction: {a['obstruction']}")
        lines.append(f"- Supporters: {', '.join(a['supporters'])}")
        lines.append("")
    if len(top_analogs) > 5:
        lines.append("## Honourable mentions")
        for a in top_analogs[5:10]:
            lines.append(
                f"- {a['analog_problem']} (technique: {a['named_technique']}, "
                f"confidence {a['confidence']}/5)"
            )
        lines.append("")
    lines.append("## Full debate transcript")
    lines.append("")
    lines.append(transcript.strip() or "_(no transcript)_")
    return "\n".join(lines)


def run_stage2(
    problem_id: str,
    models: list[str],
    rounds: int = 1,
    timeout: int = 300,
    force: bool = False,
) -> dict:
    runs_dir = RUNS_DIR
    pdir = runs_dir / problem_id
    if not pdir.exists():
        raise SystemExit(
            f"[stage2] runs dir does not exist for {problem_id}. "
            f"Run Stage 1 first."
        )
    card = json.loads((pdir / "problem_card.json").read_text())
    lit_md = (pdir / "01_literature.md").read_text()

    transcript = call_debate(
        problem_id, card, lit_md, models, rounds, timeout, force
    )
    top = consolidate(transcript, card.get("domain", "nt"))
    md = render_markdown(problem_id, card, transcript, top, models)
    (pdir / "02_analogies.md").write_text(md)

    payload = {
        "problem_id": problem_id,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "models_consulted": models,
        "top_analogs": top,
        "transcript_path": str((pdir / "02_analogies.md").resolve()),
    }
    (pdir / "02_analogies.json").write_text(json.dumps(payload, indent=2))
    print(
        f"[stage2] {problem_id}: {len(top)} consolidated analogs -> "
        f"{pdir / '02_analogies.md'}",
        file=sys.stderr,
    )
    return payload


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Stage 2 — Analogy Mining")
    p.add_argument("--problem-id", required=True)
    p.add_argument("--models", default="grok,gemini,codex")
    p.add_argument("--rounds", type=int, default=1)
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--force", action="store_true")
    args = p.parse_args(argv)
    models = [m.strip() for m in args.models.split(",") if m.strip()]
    run_stage2(args.problem_id, models, args.rounds, args.timeout, args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
