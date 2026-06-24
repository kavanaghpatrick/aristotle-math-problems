#!/usr/bin/env python3
"""
Aristotle informal-mode adapter.

Purpose
-------
Submit a bare gap sketch to Aristotle's informal-reasoner subsystem (subsystem
#2 per the W8 audit: lemma-based NL → autoformalize → REPL feedback loop). This
is the lane that solved Erdős #124 (Boris Alexeev, ~6h, Dec 2025) from a bare
problem statement, and E728 (Barreto + GPT-5.2 Pro, Jan 2026, paired strategy).

Discovery (I9, 2026-05-30; SDK now 2.0.0)
-----------------------------------------
As of the I9 audit, aristotlelib 0.7.0 exposed exactly ONE submission endpoint:

    Project.create(prompt: str, tar_file_path: Path | None = None) -> Project

aristotlelib 2.0.0 (current) adds `Project.create_from_directory()` and the
multi-turn `Project.ask()`, but this module still submits via `Project.create()`.
There is still no separate `Project.from_informal()` / `Project.solve_informal()`
or `aristotle informal` CLI subcommand; `aristotle submit "<prompt>"` and
`aristotle formalize <file>` both ultimately call `Project.create()`.

What distinguishes "informal mode" from "formalize mode" on the SERVER SIDE is
the SHAPE of the prompt:

  formalize / MCGS-only:  prompt is or contains `theorem foo : ... := by sorry`
                          (Lean scaffold, ~5-30 lines, no NL proof)
  informal mode:          prompt is a natural-language problem statement,
                          optionally with an informal proof outline and
                          candidate lemma list (no `by sorry` required, no
                          Lean scaffold required)

This adapter assembles the *informal* shape of the prompt from a bare sketch +
optional `.fusion.json` companion, then submits via the same SDK call. The
discriminator at the DB layer is `informal_mode_used=1` and `lane='informal'`,
set by the caller (`safe_aristotle_submit.py --informal-mode`).

CLI
---
    python3 aristotle_informal.py <sketch.txt>                          \\
            [--fusion-json <companion.fusion.json>]                     \\
            [--paired-llm <name>]                                       \\
            [--id-out <file>]                                           \\
            [--print-prompt]                                            \\
            [--dry-run]

Returns the project UUID on stdout (one line) on success.

Integration
-----------
`safe_aristotle_submit.py` is the canonical entry point. When invoked with
`--fusion-lane` AND a sibling `<sketch>.fusion.json` exists AND that JSON
contains a non-empty `strategy_outline` (or legacy `informal_proof_outline`)
field, the safe-submit wrapper SHOULD delegate prompt construction to this
adapter (via `build_informal_prompt()`) before calling `Project.create()`.
That integration is described in
`docs/infrastructure_changes_may30/I9_informal_mode.md`.

References
----------
- docs/aristotle_usage_guide.md §3.4 (INFORMAL lane)
- docs/research_fusion_pipeline_design.md §3 (FUSION lane companion)
- W8 finding (May 30 2026): three Aristotle subsystems, informal reasoner
  unused by our pipeline -> 0.8% hit rate vs Harmonic's 12 Erdős in 90d
"""

from __future__ import annotations

import argparse
import asyncio
import json
import logging
import os
import sys
from pathlib import Path
from typing import Any

# Repo-internal: safe_aristotle_submit's tracking-log helper, used to record
# the submission in `aristotle_submission_log.jsonl` like every other submit
# path does.  We import lazily to avoid a hard dependency cycle when this
# script is imported as a library.
MATH_DIR = Path(__file__).resolve().parent.parent


def _log_transaction(action: str, details: dict) -> None:
    """Append to aristotle_submission_log.jsonl (best-effort, never raises)."""
    try:
        from datetime import datetime
        entry = {
            "timestamp": datetime.now().isoformat(),
            "action": action,
            "details": details,
        }
        log_path = MATH_DIR / "aristotle_submission_log.jsonl"
        with open(log_path, 'a') as f:
            f.write(json.dumps(entry) + '\n')
    except Exception:
        pass  # never block the submission for a logging failure


# ---------------------------------------------------------------------------
# Companion schema
# ---------------------------------------------------------------------------

# Fields we recognize on a .fusion.json companion. We accept BOTH the design-doc
# names (strategy_outline / key_lemmas) AND the alternate names mentioned in the
# task brief (informal_proof_outline / candidate_lemmas) so the adapter works
# regardless of which schema variant the caller wrote.
STRATEGY_OUTLINE_FIELDS = ("strategy_outline", "informal_proof_outline")
KEY_LEMMAS_FIELDS = ("key_lemmas", "candidate_lemmas")
LITERATURE_FIELDS = ("cross_domain_literature", "literature_citations",
                     "seminal_paper_arxiv")
ANALOGY_FIELDS = ("primary_analogy", "analogy", "cross_domain_analogy")
TECHNIQUE_FIELDS = ("named_technique", "technique", "named_techniques")


def _first_present(d: dict, candidates: tuple[str, ...]) -> Any:
    for k in candidates:
        if k in d and d[k] not in (None, "", []):
            return d[k]
    return None


def load_fusion_companion(path: Path) -> dict:
    """Load a `.fusion.json` companion and return the parsed dict.

    Returns {} if the file does not exist; raises ValueError if it is
    unreadable or malformed JSON.
    """
    if not path.exists():
        return {}
    try:
        text = path.read_text()
        data = json.loads(text)
    except (OSError, json.JSONDecodeError) as e:
        raise ValueError(f"Companion {path.name} unreadable / invalid JSON: {e}")
    if not isinstance(data, dict):
        raise ValueError(f"Companion {path.name} must be a JSON object, got {type(data).__name__}")
    return data


# ---------------------------------------------------------------------------
# Prompt assembly: the heart of the adapter
# ---------------------------------------------------------------------------

# Marker block that flips Aristotle's server-side routing toward the informal
# reasoner.  Empirically, the routing is driven by the *content shape* of the
# prompt: a prompt that opens with a natural-language problem statement (rather
# than `theorem foo : ... := by sorry`) is taken to be an informal request.
#
# The wrapper below makes the intent unambiguous to the server-side router and
# self-documenting to anyone reading the project description in the Aristotle
# dashboard.  The phrasing is conservative: we ask Aristotle to *prove* (not to
# *formalize*) and we do not include a Lean scaffold in the prompt body.
_INFORMAL_HEADER = (
    "INFORMAL-MODE SUBMISSION\n"
    "------------------------\n"
    "Please attack the problem stated below using your informal reasoner: "
    "produce a natural-language proof first, decompose it into lemmas, then "
    "autoformalize. Do NOT treat this as a pure formalize-only task; the goal "
    "is to discover the proof, not to mechanically translate one.\n"
)


def build_informal_prompt(sketch_text: str,
                          fusion: dict | None = None,
                          paired_llm: str | None = None) -> str:
    """Build an informal-mode prompt for `Project.create(prompt=...)`.

    Layout:
      1. INFORMAL-MODE header (routing hint to Aristotle server)
      2. The problem statement, transformed to remove the Lean `by sorry`
         scaffold if present (so the prompt does NOT look like a formalize
         request).
      3. Optional informal proof outline (from fusion.strategy_outline)
      4. Optional candidate-lemma list (from fusion.key_lemmas)
      5. Optional cross-domain analogy / named technique / literature pointer
      6. paired_llm provenance footer (audit trail)

    The transformed Lean statement is preserved verbatim in a quoted block so
    Aristotle can pick it up for autoformalization, but it is not the leading
    content.  This is the structural difference from the BARE lane.
    """
    fusion = fusion or {}

    # Split sketch into front matter (OPEN GAP, English statement, Status) and
    # the Lean theorem block (if present).  We keep the Lean block but
    # de-emphasize it.
    nl_lines: list[str] = []
    lean_lines: list[str] = []
    in_lean_block = False
    for line in sketch_text.splitlines():
        stripped = line.strip()
        # Heuristic: a line that starts with `theorem ` or contains `:= by` is
        # part of the Lean theorem block.
        if stripped.startswith("theorem ") or stripped.startswith("lemma ") \
                or stripped.startswith("def ") or stripped.startswith("import "):
            in_lean_block = True
        if in_lean_block:
            lean_lines.append(line)
            if ":= by sorry" in line or stripped == "sorry":
                in_lean_block = False
        else:
            nl_lines.append(line)

    nl_part = "\n".join(nl_lines).strip()
    lean_part = "\n".join(lean_lines).strip()

    parts: list[str] = [_INFORMAL_HEADER, "## Problem Statement\n", nl_part]

    # Section 3: informal proof outline.  Falsifications welcome — Aristotle's
    # informal reasoner can produce a disproof outline too.
    outline = _first_present(fusion, STRATEGY_OUTLINE_FIELDS)
    if outline:
        parts.append("\n## Informal Proof Outline (from paired strategist)\n")
        parts.append(str(outline).strip())
        parts.append(
            "\n*Note: This outline is a starting point. Aristotle should "
            "verify, refute, or improve it as part of solving the problem.*"
        )

    # Section 4: candidate lemmas.
    lemmas = _first_present(fusion, KEY_LEMMAS_FIELDS)
    if lemmas:
        parts.append("\n## Candidate Lemmas\n")
        if isinstance(lemmas, list):
            for i, lem in enumerate(lemmas, 1):
                if isinstance(lem, dict):
                    name = lem.get("name", f"L{i}")
                    stmt = lem.get("statement") or lem.get("body") or ""
                    just = lem.get("justification") or lem.get("rationale") or ""
                    parts.append(f"**{name}.** {stmt}")
                    if just:
                        parts.append(f"  _Justification:_ {just}")
                else:
                    parts.append(f"{i}. {lem}")
        else:
            parts.append(str(lemmas).strip())

    # Section 5: analogy / technique / literature pointers.
    analogy = _first_present(fusion, ANALOGY_FIELDS)
    technique = _first_present(fusion, TECHNIQUE_FIELDS)
    literature = _first_present(fusion, LITERATURE_FIELDS)
    if analogy or technique or literature:
        parts.append("\n## Cross-Domain Context\n")
        if analogy:
            parts.append(f"- **Primary analogy:** {analogy}")
        if technique:
            parts.append(f"- **Named technique:** {technique}")
        if literature:
            if isinstance(literature, list):
                for lit in literature:
                    parts.append(f"- **Literature:** {lit}")
            else:
                parts.append(f"- **Literature:** {literature}")

    # Section 6: keep the Lean statement available verbatim, but at the bottom
    # and clearly marked as a target signature rather than the request itself.
    if lean_part:
        parts.append(
            "\n## Target Lean Statement (for autoformalization)\n"
            "When the informal proof is found, autoformalize against this "
            "exact signature:\n"
        )
        parts.append("```lean\n" + lean_part + "\n```")

    # Footer: provenance.
    if paired_llm:
        parts.append(
            f"\n---\n_Strategy outline produced by `{paired_llm}` (paired LLM)._"
        )

    return "\n".join(parts).strip() + "\n"


# ---------------------------------------------------------------------------
# Submission (async, uses aristotlelib 2.0.0)
# ---------------------------------------------------------------------------

async def submit_informal(prompt: str, *, description: str | None = None) -> str:
    """Submit `prompt` to Aristotle via `Project.create`.  Returns project UUID.

    This is the *single* Aristotle API call this adapter makes.  No tarball, no
    `aristotle formalize` subcommand — the difference from a BARE submission is
    purely in the prompt shape constructed above.
    """
    # Import here so `--help` works without ARISTOTLE_API_KEY set.
    from aristotlelib import Project, set_api_key  # type: ignore

    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if not api_key:
        raise RuntimeError("ARISTOTLE_API_KEY environment variable not set")
    set_api_key(api_key)

    project = await Project.create(prompt=prompt)
    uuid = project.project_id

    _log_transaction("informal_submit", {
        "project_id": uuid,
        "description": description or "(no description)",
        "prompt_chars": len(prompt),
        "prompt_first_120": prompt[:120].replace("\n", " "),
    })
    return uuid


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _cli() -> int:
    p = argparse.ArgumentParser(
        prog="aristotle_informal.py",
        description="Submit a bare sketch + optional .fusion.json companion "
                    "to Aristotle's informal reasoner.",
    )
    p.add_argument("sketch", type=Path,
                   help="Path to bare gap sketch (.txt). Used verbatim as the "
                        "problem statement.")
    p.add_argument("--fusion-json", type=Path, default=None,
                   help="Optional .fusion.json companion with strategy_outline "
                        "and key_lemmas.")
    p.add_argument("--paired-llm", type=str, default=None,
                   help="Name of the strategy LLM that produced the .fusion.json "
                        "outline (audit trail). E.g. 'gpt-5.2-pro', 'codex'.")
    p.add_argument("--id-out", type=Path, default=None,
                   help="If set, write the project UUID to this file in the "
                        "same format as safe_aristotle_submit.py.")
    p.add_argument("--print-prompt", action="store_true",
                   help="Print the assembled informal-mode prompt and exit "
                        "(no submission).")
    p.add_argument("--dry-run", action="store_true",
                   help="Assemble the prompt and validate inputs, but do NOT "
                        "submit to Aristotle.")
    args = p.parse_args()

    if not args.sketch.exists() or not args.sketch.is_file():
        print(f"ERROR: sketch file not found: {args.sketch}", file=sys.stderr)
        return 2

    sketch_text = args.sketch.read_text()

    fusion: dict = {}
    if args.fusion_json is not None:
        try:
            fusion = load_fusion_companion(args.fusion_json)
        except ValueError as e:
            print(f"ERROR: {e}", file=sys.stderr)
            return 2

    prompt = build_informal_prompt(
        sketch_text=sketch_text,
        fusion=fusion,
        paired_llm=args.paired_llm,
    )

    if args.print_prompt:
        print(prompt)
        return 0

    if args.dry_run:
        print(f"[dry-run] assembled prompt: {len(prompt)} chars")
        print(f"[dry-run] fusion fields used: "
              f"strategy_outline={'yes' if _first_present(fusion, STRATEGY_OUTLINE_FIELDS) else 'no'}, "
              f"key_lemmas={'yes' if _first_present(fusion, KEY_LEMMAS_FIELDS) else 'no'}")
        return 0

    # Live submission.
    try:
        uuid = asyncio.run(submit_informal(
            prompt=prompt,
            description=args.sketch.stem,
        ))
    except Exception as e:
        logging.exception("Submission failed")
        print(f"ERROR: submission failed: {e}", file=sys.stderr)
        return 1

    print(uuid)

    if args.id_out is not None:
        from datetime import datetime
        with open(args.id_out, 'w') as f:
            f.write(f"{uuid}\n")
            f.write(f"# Task: {args.sketch.stem}\n")
            f.write(f"# Mode: INFORMAL (aristotle_informal.py)\n")
            if args.paired_llm:
                f.write(f"# Paired LLM: {args.paired_llm}\n")
            f.write(f"# Submitted: {datetime.now().isoformat()}\n")

    return 0


if __name__ == "__main__":
    sys.exit(_cli())
