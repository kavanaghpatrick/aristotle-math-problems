#!/usr/bin/env python3
"""
subsystem_engagement_classifier.py
==================================

Classifies whether an Aristotle artifact invoked subsystem #1 (MCGS formalizer)
or subsystem #2 (informal lemma-based reasoner) — or whether the signals are
mixed (ambiguous).

This implements the S10 validation comparison framework. It is conservative:
when signals are mixed, the output is "ambiguous" rather than guessing.

Background (see I9 spec, docs/infrastructure_changes_may30/I9_informal_mode.md):

  Aristotle 0.7.0 exposes ONE submission endpoint. The choice of subsystem is
  driven by prompt shape:

  - Subsystem #1 (MCGS, formalizer): Lean theorem statement attached as a
    tarball, NL portion is treated as commentary. Output is typically a tactic
    proof, often closed by `native_decide`/`decide`/`simp`-only, and the
    ARISTOTLE_SUMMARY.md describes the tactic structure ("Proof strategy:
    native_decide handles ...").

  - Subsystem #2 (informal reasoner): NL problem statement, no Lean tarball.
    Aristotle generates a free-form NL proof first, decomposes it into lemmas,
    autoformalizes each lemma, and runs a REPL feedback loop. The
    ARISTOTLE_SUMMARY.md will (per the I9 smoke test) contain an explicit
    "Informal proof:" or "Informal argument:" / "Strategy:" section with
    multi-sentence math prose, followed by a separate "Formalization:" or
    "Lean encoding:" section, then the actual Lean snippet.

The four validation criteria from S10:

  C1: Informal proof section present in ARISTOTLE_SUMMARY.md
  C2: Separate formalization / Lean-encoding section
  C3: Substantial NL reasoning (≥ 30 words in identified informal sections)
  C4: Theorem proved via Mathlib lemma application, not pure
      native_decide/decide/simp

Hits on all four => "informal_reasoner".
Zero on all four AND theorem proved by `native_decide`/`decide`/`simp`-only or
  unresolved with `by sorry` => "formalizer_only".
Anything else => "ambiguous".

CLI
---

    python3 scripts/subsystem_engagement_classifier.py <artifact_dir>
    python3 scripts/subsystem_engagement_classifier.py <artifact_dir> --json
    python3 scripts/subsystem_engagement_classifier.py <artifact_dir> --pretty

The `artifact_dir` must contain `ARISTOTLE_SUMMARY.md`. If you pass a directory
that contains a subdirectory of the form `<uuid>_aristotle`, the classifier
will descend into that subdirectory automatically.

Output (JSON):

    {
      "artifact_dir": "<absolute path>",
      "uuid": "<inferred uuid or null>",
      "subsystem_engaged": "formalizer_only" | "informal_reasoner" | "ambiguous",
      "evidence_signals": [ "<signal>", ... ],
      "informal_proof_section_present": bool,
      "separate_formalization_section_present": bool,
      "nl_reasoning_word_count": int,
      "mathlib_modules_imported": [ "Mathlib.NumberTheory.ArithmeticFunction", ... ],
      "validation_criteria_hit": [ "C1", "C2", ... ]
    }

Public API
----------

    from subsystem_engagement_classifier import classify_artifact

    result = classify_artifact(Path("submissions/nu4_final/i9_extracted/..."))
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path


# ---------------------------------------------------------------------------
# Signal definitions
# ---------------------------------------------------------------------------

# Header markers (case-insensitive substring match) that indicate the writer
# of the ARISTOTLE_SUMMARY.md framed the work as an NL-first proof discovery.
INFORMAL_PROOF_HEADERS = [
    "informal proof",
    "informal argument",
    "informal reasoning",
    "natural-language proof",
    "natural language proof",
    "english proof",
    "english argument",
    # Less specific — present in BOTH modes, so we down-weight (see below).
    # "proof strategy",
    # "proof sketch",
    # "strategy",
]

# Headers that mark a SEPARATE formalization/Lean-encoding section, distinct
# from the informal proof section.
FORMALIZATION_HEADERS = [
    "formalization",
    "lean encoding",
    "lean formalization",
    "lean proof",
    "formal proof",
    "in lean",
]

# Markers that the theorem was closed by a brute-force computational tactic
# only — characteristic of MCGS / formalizer-only submissions.
COMPUTATIONAL_TACTIC_MARKERS = [
    "native_decide",
    "by decide",
    "by simp",
    "by rfl",
]

# Markers that the theorem was left open (typical of failed MCGS).
SORRY_MARKERS = [
    "sorry",
    "by sorry",
    "still has",
    "remaining sorry",
    "one sorry",
    "sorry remaining",
]

# Markers that the prompt itself was the informal-mode prompt (matches the
# header I9 generates).
INFORMAL_PROMPT_HEADER = "INFORMAL-MODE SUBMISSION"


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class ClassificationResult:
    artifact_dir: str
    uuid: str | None
    subsystem_engaged: str  # "formalizer_only" | "informal_reasoner" | "ambiguous"
    evidence_signals: list[str] = field(default_factory=list)
    informal_proof_section_present: bool = False
    separate_formalization_section_present: bool = False
    nl_reasoning_word_count: int = 0
    mathlib_modules_imported: list[str] = field(default_factory=list)
    validation_criteria_hit: list[str] = field(default_factory=list)
    # Diagnostics (not part of S10 spec but useful for debugging).
    summary_present: bool = True
    summary_word_count: int = 0
    main_lean_present: bool = True
    has_native_decide_only_proof: bool = False
    has_unresolved_sorry: bool = False
    # The set of informal-section headers actually found.
    informal_headers_found: list[str] = field(default_factory=list)
    formalization_headers_found: list[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _resolve_artifact_dir(artifact_dir: Path) -> Path:
    """If artifact_dir contains a `<uuid>_aristotle/` (or `*_aristotle/`)
    child, descend to find ARISTOTLE_SUMMARY.md.

    This is the layout used by `aristotlelib.Project.get_files()`.
    """
    if (artifact_dir / "ARISTOTLE_SUMMARY.md").exists():
        return artifact_dir
    # Look for any *_aristotle subdirectory.
    if artifact_dir.exists() and artifact_dir.is_dir():
        for child in sorted(artifact_dir.iterdir()):
            if child.is_dir() and child.name.endswith("_aristotle"):
                if (child / "ARISTOTLE_SUMMARY.md").exists():
                    return child
    return artifact_dir  # caller will see ARISTOTLE_SUMMARY.md missing


def _infer_uuid(artifact_dir: Path) -> str | None:
    """Try to infer the UUID from the directory or filenames."""
    # Pattern: <uuid>_aristotle
    m = re.match(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})_aristotle",
                 artifact_dir.name)
    if m:
        return m.group(1)
    # Try inside ARISTOTLE_SUMMARY.md ("Summary of changes for run <uuid>")
    summary = artifact_dir / "ARISTOTLE_SUMMARY.md"
    if summary.exists():
        for line in summary.read_text(encoding="utf-8", errors="replace").splitlines():
            m = re.search(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", line)
            if m:
                return m.group(1)
    return None


def _find_lean_main(artifact_dir: Path) -> Path | None:
    """Locate the primary Lean file (typically RequestProject/Main.lean)."""
    candidates = [
        artifact_dir / "RequestProject" / "Main.lean",
    ]
    for c in candidates:
        if c.exists():
            return c
    # Fallback: any .lean file with a `theorem` keyword.
    for lf in artifact_dir.rglob("*.lean"):
        if lf.name.startswith("_mcp_snippet_"):
            continue  # ignore MCP scratch snippets
        return lf
    return None


def _extract_mathlib_imports(lean_text: str) -> list[str]:
    """Pull `import Mathlib.X.Y.Z` lines (and a single `import Mathlib`)."""
    imports: list[str] = []
    for line in lean_text.splitlines():
        line = line.strip()
        m = re.match(r"^import\s+(Mathlib(\.[\w]+)*)\s*$", line)
        if m:
            imports.append(m.group(1))
    return imports


def _find_headers(text: str, candidates: list[str]) -> list[str]:
    """Return the candidate headers actually present (case-insensitive).

    A "header" is any line that contains the candidate as a substring AND
    appears either with markdown header markers (#, **) or with a trailing
    colon. This avoids matching e.g. "informal proof" inside a sentence body.
    """
    found: list[str] = []
    lower = text.lower()
    for cand in candidates:
        cand_l = cand.lower()
        if cand_l not in lower:
            continue
        # Look for a line where this substring is in header-shape.
        for line in text.splitlines():
            ll = line.lower().strip()
            if cand_l not in ll:
                continue
            # Header-shape heuristics:
            is_md_header = ll.startswith("#")
            is_bold = ll.startswith("**") and "**" in ll[2:]
            has_colon = (cand_l + ":") in ll or ll.endswith(":") and cand_l in ll
            # Or it's the first non-empty content of a paragraph-like marker
            if is_md_header or is_bold or has_colon:
                found.append(cand)
                break
    return found


def _word_count(text: str) -> int:
    return len(re.findall(r"\b[\w'-]+\b", text))


def _extract_nl_sections(text: str, informal_headers: list[str]) -> str:
    """Extract NL prose under the informal-proof headers.

    Returns the concatenated body text under each matched informal header,
    stopping at the next markdown header of equal-or-shallower depth (or at the
    next major section).
    """
    if not informal_headers:
        return ""
    lines = text.splitlines()
    n = len(lines)
    cursor = 0
    nl_chunks: list[str] = []
    informal_lower = [h.lower() for h in informal_headers]

    while cursor < n:
        line = lines[cursor]
        stripped = line.strip()
        ll = stripped.lower()
        # Detect a header that starts an informal section.
        is_header_line = stripped.startswith("#") or (stripped.startswith("**") and stripped.endswith("**"))
        if is_header_line and any(h in ll for h in informal_lower):
            # Determine header level.
            if stripped.startswith("#"):
                level = len(stripped) - len(stripped.lstrip("#"))
            else:
                level = 99  # treat bold-as-header as deepest
            # Walk forward collecting body until we hit the next header of
            # level <= this one OR a fenced code block.
            body: list[str] = []
            cursor += 1
            while cursor < n:
                cur = lines[cursor].rstrip()
                cur_strip = cur.strip()
                if cur_strip.startswith("```"):
                    # Skip code block (NOT counted as NL reasoning).
                    cursor += 1
                    while cursor < n and not lines[cursor].strip().startswith("```"):
                        cursor += 1
                    cursor += 1
                    continue
                if cur_strip.startswith("#"):
                    new_level = len(cur_strip) - len(cur_strip.lstrip("#"))
                    if new_level <= level:
                        break
                body.append(cur)
                cursor += 1
            nl_chunks.append("\n".join(body))
            continue
        cursor += 1

    return "\n\n".join(nl_chunks)


def _has_pure_computational_tactic(lean_text: str) -> bool:
    """Check whether every `theorem ... := by` block resolves purely via
    native_decide / decide / simp / rfl.

    Heuristic: if the file contains `native_decide` and contains no other
    tactic invocations that look like Mathlib-lemma applications (`exact ...`,
    `apply ...`, `rw [...]`, `unfold ...`), classify as pure-computational.
    Otherwise: not pure-computational.

    This is intentionally tight to avoid false positives.
    """
    if not lean_text.strip():
        return False
    lower = lean_text.lower()
    has_computational = any(m in lean_text for m in ("native_decide", "by decide", "by rfl"))
    if not has_computational:
        return False
    # Check for lemma-application tactics. A real Mathlib proof typically uses
    # at least one of these.
    lemma_app_signs = [
        re.compile(r"\bexact\s+[A-Z]"),     # `exact Nat.exists_infinite_primes`
        re.compile(r"\bapply\s+[A-Z]"),
        re.compile(r"\brefine\s"),
        re.compile(r"\brw\s*\["),
        re.compile(r"\bsimp\s*only\s*\["),
        re.compile(r"\bgrind\b"),
        re.compile(r"\binduction\s"),
        re.compile(r"\bcases\s"),
        re.compile(r"\brcases\s"),
        re.compile(r"\bobtain\s"),
        re.compile(r"\bhave\s+\w+\s*:"),
        re.compile(r"\blinarith\b"),
        re.compile(r"\bomega\b"),
    ]
    for pat in lemma_app_signs:
        if pat.search(lean_text):
            return False
    return True


def _has_unresolved_sorry(lean_text: str) -> bool:
    """True iff a `theorem`/`lemma` body still contains a `sorry`."""
    if not lean_text:
        return False
    # Strip line comments.
    cleaned = re.sub(r"--.*", "", lean_text)
    # The Lean keyword `sorry` standalone (not part of `_sorry_` etc.).
    return bool(re.search(r"\bsorry\b", cleaned))


# ---------------------------------------------------------------------------
# Core classifier
# ---------------------------------------------------------------------------


def classify_artifact(artifact_dir: Path) -> ClassificationResult:
    """Classify an extracted Aristotle artifact directory.

    The directory must contain (directly or in a `<uuid>_aristotle/` child) an
    `ARISTOTLE_SUMMARY.md` file. The primary Lean file (typically
    `RequestProject/Main.lean`) is also inspected if present.
    """
    artifact_dir = artifact_dir.resolve()
    actual_dir = _resolve_artifact_dir(artifact_dir)
    summary_path = actual_dir / "ARISTOTLE_SUMMARY.md"
    uuid = _infer_uuid(actual_dir)

    result = ClassificationResult(
        artifact_dir=str(actual_dir),
        uuid=uuid,
        subsystem_engaged="ambiguous",
    )

    if not summary_path.exists():
        result.summary_present = False
        result.subsystem_engaged = "ambiguous"
        result.evidence_signals.append("missing:ARISTOTLE_SUMMARY.md")
        return result

    summary_text = summary_path.read_text(encoding="utf-8", errors="replace")
    result.summary_word_count = _word_count(summary_text)

    # --- header detection ---
    informal_headers = _find_headers(summary_text, INFORMAL_PROOF_HEADERS)
    formalization_headers = _find_headers(summary_text, FORMALIZATION_HEADERS)
    result.informal_headers_found = informal_headers
    result.formalization_headers_found = formalization_headers
    result.informal_proof_section_present = bool(informal_headers)
    result.separate_formalization_section_present = bool(formalization_headers)

    # --- NL prose under informal sections ---
    nl_text = _extract_nl_sections(summary_text, informal_headers)
    result.nl_reasoning_word_count = _word_count(nl_text)

    # --- Lean file inspection ---
    lean_path = _find_lean_main(actual_dir)
    if lean_path is None:
        result.main_lean_present = False
        lean_text = ""
    else:
        lean_text = lean_path.read_text(encoding="utf-8", errors="replace")
    result.mathlib_modules_imported = _extract_mathlib_imports(lean_text)
    result.has_native_decide_only_proof = _has_pure_computational_tactic(lean_text)
    result.has_unresolved_sorry = _has_unresolved_sorry(lean_text)

    # --- evidence signals ---
    signals = result.evidence_signals
    if informal_headers:
        signals.append(f"informal_header:{','.join(informal_headers)}")
    if formalization_headers:
        signals.append(f"formalization_header:{','.join(formalization_headers)}")
    if result.nl_reasoning_word_count > 0:
        signals.append(f"nl_words={result.nl_reasoning_word_count}")
    if INFORMAL_PROMPT_HEADER in summary_text:
        signals.append("informal_mode_prompt_echo")
    if result.has_native_decide_only_proof:
        signals.append("pure_computational_tactic")
    if result.has_unresolved_sorry:
        signals.append("unresolved_sorry")
    if result.mathlib_modules_imported:
        signals.append(f"mathlib_imports={len(result.mathlib_modules_imported)}")

    # --- validation criteria (S10) ---
    crit: list[str] = []
    if result.informal_proof_section_present:
        crit.append("C1")
    if result.separate_formalization_section_present:
        crit.append("C2")
    if result.nl_reasoning_word_count >= 30:
        crit.append("C3")
    # C4: theorem proved via Mathlib lemma application, NOT pure
    # native_decide / decide / simp. Requires a Lean file with imports AND not
    # being pure-computational.
    if lean_text and not result.has_native_decide_only_proof and not result.has_unresolved_sorry:
        if result.mathlib_modules_imported:
            crit.append("C4")
    result.validation_criteria_hit = crit

    # --- classification ---
    # Strong "formalizer_only" signatures:
    #   - no informal headers AND no separate formalization section
    #   - AND (proof is pure-computational OR proof is unresolved by sorry)
    no_informal_signal = (
        not result.informal_proof_section_present
        and not result.separate_formalization_section_present
        and result.nl_reasoning_word_count == 0
    )
    proof_shape_is_formalizer_like = (
        result.has_native_decide_only_proof or result.has_unresolved_sorry
    )

    # Strong "informal_reasoner" signatures: all four S10 criteria.
    if len(crit) >= 3 and "C1" in crit and "C2" in crit:
        # Need C1 (informal header) + C2 (separate formalization) + (C3 OR C4).
        # ≥3 criteria with C1 and C2 means substantial NL + lemma-app or
        # substantial NL + separate sections.
        result.subsystem_engaged = "informal_reasoner"
    elif no_informal_signal and proof_shape_is_formalizer_like:
        result.subsystem_engaged = "formalizer_only"
    else:
        result.subsystem_engaged = "ambiguous"

    return result


# ---------------------------------------------------------------------------
# CLI entrypoint
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Classify an Aristotle artifact as formalizer_only / "
                    "informal_reasoner / ambiguous."
    )
    parser.add_argument("artifact_dir", help="Path to extracted artifact directory")
    parser.add_argument("--json", action="store_true",
                        help="Print compact JSON (default).")
    parser.add_argument("--pretty", action="store_true",
                        help="Pretty-print JSON with 2-space indent.")
    args = parser.parse_args()

    p = Path(args.artifact_dir)
    if not p.exists():
        print(f"ERROR: artifact directory does not exist: {p}", file=sys.stderr)
        return 2

    result = classify_artifact(p)
    payload = asdict(result)
    if args.pretty:
        print(json.dumps(payload, indent=2))
    else:
        print(json.dumps(payload))
    return 0


if __name__ == "__main__":
    sys.exit(main())
