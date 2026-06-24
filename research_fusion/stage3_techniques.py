#!/usr/bin/env python3
"""Stage 3 — Technique Transfer.

For each top analog from Stage 2, asks Codex (gpt-5.5 via codex CLI) for a
single technique card matching schemas/technique_card.schema.json. Computes
fit_score = (# YES + 0.5 * # PARTIAL) / total_requirements. Emits a
03_techniques.md + 03_techniques.json + fusion_candidate.json.

Usage:
    python3 -m research_fusion.stage3_techniques --problem-id erdos_938
    python3 -m research_fusion.stage3_techniques \\
        --problem-id erdos_938 --max-cards 5 --force
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

THIS_DIR = Path(__file__).resolve().parent
RUNS_DIR = THIS_DIR / "runs"
PROMPT_PATH = THIS_DIR / "prompts" / "stage3_techniques.md"
CACHE_TTL = 7 * 24 * 60 * 60


def _cache_dir(problem_id: str) -> Path:
    d = RUNS_DIR / problem_id / ".cache"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _cache_key(prompt: str) -> str:
    return hashlib.sha256(prompt.encode()).hexdigest()[:16]


def _cache_get(problem_id: str, key: str) -> str | None:
    p = _cache_dir(problem_id) / f"tech_{key}.txt"
    if not p.exists():
        return None
    if time.time() - p.stat().st_mtime > CACHE_TTL:
        return None
    return p.read_text()


def _cache_put(problem_id: str, key: str, payload: str) -> None:
    p = _cache_dir(problem_id) / f"tech_{key}.txt"
    p.write_text(payload)


# ─────────────────────────────────────────────────────────────────────────
# Codex call
# ─────────────────────────────────────────────────────────────────────────

def call_codex(prompt: str, timeout: int = 240) -> str:
    """Invoke codex CLI exec with a read-only sandbox."""
    prompt_file = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False,
        ) as f:
            f.write(prompt)
            prompt_file = f.name
        cmd = [
            "bash", "-c",
            f'codex exec --full-auto --sandbox read-only '
            f'"$(cat \'{prompt_file}\')"',
        ]
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout
        )
        out = proc.stdout.strip()
        if not out and proc.stderr:
            return f"TECHNIQUE_CARD_DECLINED: codex_stderr={proc.stderr[:400]}"
        return out or "TECHNIQUE_CARD_DECLINED: empty codex response"
    except subprocess.TimeoutExpired:
        return f"TECHNIQUE_CARD_DECLINED: codex timeout after {timeout}s"
    except FileNotFoundError:
        return "TECHNIQUE_CARD_DECLINED: codex CLI not installed"
    except Exception as exc:  # noqa: BLE001
        return f"TECHNIQUE_CARD_DECLINED: codex error {type(exc).__name__}: {exc}"
    finally:
        if prompt_file and os.path.exists(prompt_file):
            try:
                os.unlink(prompt_file)
            except OSError:
                pass


# ─────────────────────────────────────────────────────────────────────────
# Prompt build / parse
# ─────────────────────────────────────────────────────────────────────────

def build_prompt(card: dict, analog: dict) -> str:
    tpl = PROMPT_PATH.read_text()
    # String-replace (NOT .format) because the prompt contains literal JSON
    # `{...}` examples that confuse .format.
    subs = {
        "{bare_statement}": str(card.get("bare_statement", "(none)")),
        "{english_abstract}": str(card.get("what_is_known", "(none)")),
        "{home_domain}": str(card.get("domain", "nt")),
        "{analog_problem}": str(analog.get("analog_problem", "")),
        "{analog_domain}": str(analog.get("analog_domain", "")),
        "{named_technique}": str(analog.get("named_technique", "")),
        "{structural_map}": str(analog.get("structural_map", "")),
        "{obstruction}": str(analog.get("obstruction", "")),
        "{confidence}": str(analog.get("confidence", 3)),
        "{analog_id}": str(analog.get("analog_id", "A?")),
    }
    out = tpl
    for k, v in subs.items():
        out = out.replace(k, v)
    return out


def parse_card(text: str, analog: dict) -> dict | None:
    """Pull the first ```json fenced object out of Codex's response."""
    if text.strip().startswith("TECHNIQUE_CARD_DECLINED"):
        return None
    m = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text)
    if not m:
        # Try braces directly
        m = re.search(r"(\{[\s\S]*\})", text)
        if not m:
            return None
    try:
        obj = json.loads(m.group(1))
    except json.JSONDecodeError:
        return None
    if not isinstance(obj, dict):
        return None
    # Ensure source linkage to the analog.
    obj.setdefault("source_analog_id", analog.get("analog_id"))
    return obj


def recompute_fit_score(card: dict) -> float:
    matches = card.get("input_match") or []
    if not matches:
        return 0.0
    yes = sum(1 for m in matches if (m.get("match") or "").upper() == "YES")
    partial = sum(
        1 for m in matches if (m.get("match") or "").upper() == "PARTIAL"
    )
    total = len(matches)
    return round((yes + 0.5 * partial) / total, 3) if total else 0.0


def validate_card(card: dict) -> tuple[bool, str]:
    """Best-effort field-level validation against technique_card.schema.json."""
    required = ["name", "what_it_does", "input_requirements",
                "output_signature", "input_match", "fit_score"]
    for k in required:
        if k not in card:
            return False, f"missing field: {k}"
    if not isinstance(card["input_requirements"], list) or \
            len(card["input_requirements"]) < 1:
        return False, "input_requirements must be a non-empty list"
    if not isinstance(card["input_match"], list) or \
            len(card["input_match"]) != len(card["input_requirements"]):
        return False, "input_match length must equal input_requirements length"
    for m in card["input_match"]:
        if (m.get("match") or "").upper() not in {"YES", "NO", "PARTIAL"}:
            return False, f"input_match has invalid match value: {m.get('match')}"
    if not (0.0 <= float(card.get("fit_score", -1)) <= 1.0):
        return False, "fit_score not in [0,1]"
    return True, "ok"


# ─────────────────────────────────────────────────────────────────────────
# Aggregation
# ─────────────────────────────────────────────────────────────────────────

def render_markdown(problem_id: str, cards: list[dict],
                    declines: list[dict]) -> str:
    lines = [
        f"# Technique transfer — {problem_id}",
        f"Stage: 3  Candidate count: {len(cards)}  "
        f"Declined: {len(declines)}  "
        f"Generated: {datetime.utcnow().strftime('%Y-%m-%d')}",
        "",
    ]
    for i, c in enumerate(cards, 1):
        lines.append(f"## Card {i} (rank {c.get('rank', i)}, fit_score={c.get('fit_score')})")
        lines.append(f"- name: {c.get('name')}")
        sp = c.get("seminal_paper") or {}
        cite_bits = []
        if sp.get("arxiv_id"):
            cite_bits.append(f"arxiv:{sp['arxiv_id']}")
        if sp.get("doi"):
            cite_bits.append(f"doi:{sp['doi']}")
        if sp.get("citation"):
            cite_bits.append(sp["citation"])
        if sp.get("year"):
            cite_bits.append(f"year:{sp['year']}")
        lines.append(f"- seminal_paper: {' | '.join(cite_bits) or '(none)'}")
        lines.append(f"- home_domain: {c.get('home_domain', 'unknown')}")
        lines.append(f"- source_analog_id: {c.get('source_analog_id', 'n/a')}")
        lines.append(f"- what_it_does: {c.get('what_it_does', '')}")
        lines.append("- input_requirements:")
        for r, m in zip(c.get("input_requirements", []),
                        c.get("input_match", [])):
            tick = {
                "YES": "[x]", "NO": "[ ]", "PARTIAL": "[~]",
            }.get((m.get("match") or "").upper(), "[?]")
            ev = m.get("evidence", "")
            lines.append(f"  - {tick} {r}" + (f" — {ev}" if ev else ""))
        lines.append(f"- output_signature: {c.get('output_signature', '')}")
        if c.get("known_obstructions"):
            lines.append("- known_obstructions:")
            for o in c["known_obstructions"]:
                lines.append(f"  - {o}")
        lines.append("")
    if declines:
        lines.append("## Declined analogs (Codex said TECHNIQUE_CARD_DECLINED)")
        for d in declines:
            lines.append(f"- {d.get('analog_id')}: {d.get('analog_problem')} — "
                         f"{d.get('reason', 'no reason given')}")
        lines.append("")
    return "\n".join(lines)


def aggregate_fusion_candidate(
    card: dict, lit: dict, ana: dict, cards: list[dict]
) -> dict:
    pid = card["problem_id"]
    # Use repo-relative paths so I8's fusion-axis gate can resolve them.
    lit_rel = f"research_fusion/runs/{pid}/01_literature.md"
    ana_rel = f"research_fusion/runs/{pid}/02_analogies.md"
    tech_rel = f"research_fusion/runs/{pid}/03_techniques.md"
    return {
        "problem_id": pid,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "stage_outputs": {
            "literature_path": lit_rel,
            "analogies_path": ana_rel,
            "techniques_path": tech_rel,
        },
        "literature": {
            "paper_count": lit.get("paper_count", 0),
            "domains_covered": lit.get("domains_covered", []),
            "path": lit_rel,
            "papers": [
                {
                    "title": p.get("title"),
                    "authors": p.get("authors", []),
                    "arxiv_id": p.get("arxiv_id"),
                    "year": p.get("year"),
                    "domain_tag": p.get("domain_tag"),
                    "summary": (p.get("summary") or "")[:400],
                    "url": p.get("url"),
                }
                for p in (lit.get("papers") or [])[:20]
            ],
        },
        "analogies": {
            "path": ana_rel,
            "models_consulted": ana.get("models_consulted", []),
            "top_analogs": ana.get("top_analogs", [])[:5],
        },
        "technique_cards": cards,
        "honest_disclaimer": (
            "This dossier catalogs cross-domain analogs and named techniques. "
            "It does NOT claim any technique closes the gap. fit_score is a "
            "structural overlap heuristic, NOT a probability of success. "
            "Stage 4 must still write a fusion sketch that does not propose "
            "a bridge lemma."
        ),
    }


def run_stage3(
    problem_id: str,
    max_cards: int = 5,
    timeout: int = 240,
    force: bool = False,
) -> dict:
    pdir = RUNS_DIR / problem_id
    if not pdir.exists():
        raise SystemExit(f"[stage3] runs dir missing for {problem_id}")
    card = json.loads((pdir / "problem_card.json").read_text())
    lit = json.loads((pdir / "01_literature.json").read_text())
    ana = json.loads((pdir / "02_analogies.json").read_text())
    analogs = ana.get("top_analogs", [])[:max_cards]

    cards: list[dict] = []
    declines: list[dict] = []
    for a in analogs:
        prompt = build_prompt(card, a)
        ck = _cache_key(prompt)
        resp = None if force else _cache_get(problem_id, ck)
        if resp is None:
            print(f"[stage3] codex card for {a.get('analog_id')}: "
                  f"{a.get('analog_problem')}", file=sys.stderr)
            resp = call_codex(prompt, timeout=timeout)
            _cache_put(problem_id, ck, resp)
        parsed = parse_card(resp, a)
        if parsed is None:
            reason = "parse_failed"
            if resp.strip().startswith("TECHNIQUE_CARD_DECLINED"):
                reason = resp.strip()
            declines.append({
                "analog_id": a.get("analog_id"),
                "analog_problem": a.get("analog_problem"),
                "reason": reason[:300],
            })
            continue
        # Recompute fit_score from the match table for honesty.
        parsed["fit_score"] = recompute_fit_score(parsed)
        ok, msg = validate_card(parsed)
        if not ok:
            declines.append({
                "analog_id": a.get("analog_id"),
                "analog_problem": a.get("analog_problem"),
                "reason": f"validation_failed: {msg}",
            })
            continue
        cards.append(parsed)

    # Rank by fit_score desc.
    cards.sort(key=lambda c: c.get("fit_score", 0.0), reverse=True)
    for i, c in enumerate(cards, 1):
        c["rank"] = i

    md = render_markdown(problem_id, cards, declines)
    (pdir / "03_techniques.md").write_text(md)
    (pdir / "03_techniques.json").write_text(json.dumps(
        {
            "problem_id": problem_id,
            "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "technique_cards": cards,
            "declines": declines,
        },
        indent=2,
    ))

    fusion = aggregate_fusion_candidate(card, lit, ana, cards)
    (pdir / "fusion_candidate.json").write_text(json.dumps(fusion, indent=2))
    print(
        f"[stage3] {problem_id}: {len(cards)} technique cards, "
        f"{len(declines)} declines -> {pdir / '03_techniques.md'}",
        file=sys.stderr,
    )
    return {
        "problem_id": problem_id,
        "cards": cards,
        "declines": declines,
        "fusion_candidate_path": str(pdir / "fusion_candidate.json"),
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Stage 3 — Technique Transfer")
    p.add_argument("--problem-id", required=True)
    p.add_argument("--max-cards", type=int, default=5)
    p.add_argument("--timeout", type=int, default=240)
    p.add_argument("--force", action="store_true")
    args = p.parse_args(argv)
    run_stage3(args.problem_id, args.max_cards, args.timeout, args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
