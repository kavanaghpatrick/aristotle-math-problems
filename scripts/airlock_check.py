#!/usr/bin/env python3
"""airlock_check.py — FUSION-lane airlock validation.

The FUSION lane requires that ALL strategy content lives in the companion
`.fusion.json` and NONE leaks into the bare `.txt` sketch. The .txt stays
<=30 lines and contains only the open-gap statement; the .fusion.json
contains the paired-LLM dossier (named technique, bridge lemma, candidate
lemmas, informal proof outline, honest disclaimer).

This script implements the airlock: it reads both files and refuses if any
strategy token from the companion (or from the default blocklist) appears
in the .txt.

CLI:
    python3 scripts/airlock_check.py <sketch.txt> [--companion <path>]
                                                  [--blocklist <path>]
                                                  [--quiet]

Exit codes:
    0 — airlock PASSED (txt is clean)
    1 — airlock REJECTED (strategy leak detected)
    2 — invocation error (missing files, etc.)

Importable API:
    from airlock_check import run_airlock, AirlockError
    result = run_airlock(txt_path, companion_path=None, blocklist_path=None)
    # raises AirlockError on leak

Reference:
    docs/fusion_axis_companion_spec.md
    docs/infrastructure_changes_may30/I8_fusion_lane.md
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Iterable

MATH_DIR = Path(__file__).resolve().parent.parent
DEFAULT_BLOCKLIST = MATH_DIR / "scripts" / "airlock_blocklist.txt"


class AirlockError(Exception):
    """Raised when the airlock check rejects the .txt for a strategy leak.

    The exception message names the offending term and its context (so the
    author can locate it quickly).
    """


def _companion_fusion_path(input_file: Path) -> Path:
    """Return the companion .fusion.json path for a sketch.

    Convention (docs/fusion_axis_companion_spec.md): take the .txt path,
    strip its suffix, append `.fusion.json` adjacent to it.
    """
    return input_file.with_suffix(".fusion.json")


def _load_blocklist(blocklist_path: Path) -> list[str]:
    """Read the static blocklist file. One token per non-comment, non-blank line.

    Tokens are returned as-is (case-folding happens at match time).
    """
    if not blocklist_path.exists():
        return []
    tokens: list[str] = []
    with blocklist_path.open() as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            tokens.append(line)
    return tokens


def _derive_dynamic_tokens(companion: dict) -> list[str]:
    """Derive per-submission strategy tokens from the companion dossier.

    These tokens are concatenated with the static blocklist to form the full
    leak set for this specific submission. The author does not need to
    pre-register their named technique in the static list.

    Tokens harvested:
      - `named_technique`         (whole phrase)
      - first capitalised word(s) of `named_technique` (e.g. "Frey" from
        "Frey-Hellegouarch")
      - `bridge_lemma`            (only the first 6 words — the headline)
      - first 6 words of each entry in `candidate_lemmas` (the headline,
        before `: ...`)

    The intent: an author who declares `named_technique="Frey curve"` cannot
    write "Frey" in the .txt without tripping the airlock, even though
    "Frey curve" alone is what they wrote.
    """
    tokens: list[str] = []

    nt = companion.get("named_technique")
    if isinstance(nt, str) and nt.strip():
        tokens.append(nt.strip())
        # Also harvest the first sub-word — defeats `named_technique='Frey curve'`
        # being skirted by writing `Frey` alone in the .txt.
        for sub in re.split(r"[\s\-_/+]+", nt.strip()):
            sub = sub.strip()
            if len(sub) >= 4 and sub[0].isupper():
                tokens.append(sub)

    bl = companion.get("bridge_lemma")
    if isinstance(bl, str) and bl.strip():
        headline = " ".join(bl.strip().split()[:6])
        if headline:
            tokens.append(headline)

    lemmas = companion.get("candidate_lemmas") or []
    if isinstance(lemmas, list):
        for entry in lemmas:
            if not isinstance(entry, str):
                continue
            # Convention: "lemma1: short statement..." -> take chars before `:`
            # but if no colon, take the first 6 words.
            head = entry.split(":", 1)[0].strip()
            if not head or len(head) < 4:
                head = " ".join(entry.strip().split()[:6])
            if head:
                tokens.append(head)

    # De-dup while preserving order (case-insensitive)
    seen: set[str] = set()
    out: list[str] = []
    for t in tokens:
        key = t.casefold()
        if key in seen:
            continue
        seen.add(key)
        out.append(t)
    return out


def _strip_header_lines(text: str) -> str:
    """Remove the gap-header lines (`OPEN GAP:`, `Source:`, `Domain:`) and
    the `Status:` footer from the .txt body before leak-scanning.

    Rationale: those lines may legitimately reference the problem domain or
    a source file path that happens to share a token with the blocklist
    (e.g. `Source: formal-conjectures/Erdos_modular.lean` contains the word
    "modular"). We strip them to avoid false positives on metadata.
    """
    keep = []
    skip_prefixes = (
        "open gap:", "source:", "domain:", "status:", "ref:", "reference:"
    )
    for line in text.splitlines():
        s = line.strip().lower()
        if any(s.startswith(p) for p in skip_prefixes):
            continue
        keep.append(line)
    return "\n".join(keep)


def _whole_token_match(needle: str, haystack: str) -> tuple[bool, str]:
    """Case-insensitive whole-word boundary match.

    Returns (matched, context_snippet). The context snippet shows ~40 chars
    around the first match, with the match in ALL CAPS, for the error message.

    "Whole word" here means: not preceded or followed by an ASCII letter or
    digit. Adjacency to spaces, punctuation, brackets, line breaks all count
    as boundaries — which is the correct behavior for tokens that may
    contain hyphens (`Frey-Hellegouarch`) or spaces (`Frey curve`).
    """
    needle_norm = re.escape(needle.strip())
    pat = re.compile(
        r"(?<![A-Za-z0-9])(" + needle_norm + r")(?![A-Za-z0-9])",
        re.IGNORECASE,
    )
    m = pat.search(haystack)
    if not m:
        return False, ""
    start, end = m.span()
    ctx_start = max(0, start - 30)
    ctx_end = min(len(haystack), end + 30)
    ctx = haystack[ctx_start:ctx_end]
    matched_substr = haystack[start:end]
    # Highlight the matched span with brackets so the author can locate it.
    highlighted = (
        haystack[ctx_start:start]
        + "[[" + matched_substr.upper() + "]]"
        + haystack[end:ctx_end]
    ).replace("\n", " / ")
    return True, highlighted


def run_airlock(
    input_file: Path,
    companion_path: Path | None = None,
    blocklist_path: Path | None = None,
    quiet: bool = False,
) -> dict:
    """Run the airlock check. Raises AirlockError on leak.

    Args:
        input_file: the .txt sketch
        companion_path: explicit companion .fusion.json path. If None, derived
            from input_file. May not exist — in that case dynamic tokens are
            skipped and only the static blocklist is used.
        blocklist_path: explicit static blocklist file. If None, the default
            at scripts/airlock_blocklist.txt is used.
        quiet: if True, suppress per-token PASS prints (still print on leak).

    Returns:
        {"passed": True,
         "txt_lines": int,
         "static_tokens": int,
         "dynamic_tokens": int,
         "companion_present": bool}

    Raises:
        AirlockError: if any token from the merged blocklist is found in the
        body of the .txt (i.e. excluding the metadata header lines).
    """
    if not input_file.exists():
        raise AirlockError(f"sketch not found: {input_file}")

    txt_raw = input_file.read_text()
    txt_body = _strip_header_lines(txt_raw)
    txt_lines = txt_raw.count("\n") + (0 if txt_raw.endswith("\n") else 1)

    companion = None
    companion_present = False
    if companion_path is None:
        companion_path = _companion_fusion_path(input_file)

    if companion_path.exists():
        try:
            companion = json.loads(companion_path.read_text())
            if isinstance(companion, dict):
                companion_present = True
        except (OSError, json.JSONDecodeError):
            companion = None

    if blocklist_path is None:
        blocklist_path = DEFAULT_BLOCKLIST
    static_tokens = _load_blocklist(blocklist_path)

    dynamic_tokens = (
        _derive_dynamic_tokens(companion) if companion else []
    )

    merged: list[str] = []
    seen: set[str] = set()
    for t in static_tokens + dynamic_tokens:
        key = t.casefold().strip()
        if not key or key in seen:
            continue
        seen.add(key)
        merged.append(t)

    if not quiet:
        print(
            f"   [airlock] txt={input_file.name} body_lines={len(txt_body.splitlines())} "
            f"static={len(static_tokens)} dynamic={len(dynamic_tokens)} merged={len(merged)}"
        )

    # Scan
    for token in merged:
        hit, ctx = _whole_token_match(token, txt_body)
        if hit:
            raise AirlockError(
                f"airlock REJECT: token '{token}' leaked into bare .txt\n"
                f"  file: {input_file}\n"
                f"  context: ...{ctx}...\n"
                f"  fix: remove the strategy term from the .txt; keep it in "
                f"{companion_path.name} (named_technique / bridge_lemma).\n"
                f"  reference: docs/fusion_axis_companion_spec.md"
            )

    return {
        "passed": True,
        "txt_lines": txt_lines,
        "static_tokens": len(static_tokens),
        "dynamic_tokens": len(dynamic_tokens),
        "companion_present": companion_present,
    }


def _cli() -> int:
    import argparse

    parser = argparse.ArgumentParser(
        description="FUSION-lane airlock check: verify the .txt is clean of strategy.",
    )
    parser.add_argument("sketch", help="Path to the bare .txt sketch.")
    parser.add_argument("--companion", help="Path to the .fusion.json companion.",
                        default=None)
    parser.add_argument("--blocklist", help="Path to a strategy-term blocklist file.",
                        default=None)
    parser.add_argument("--quiet", action="store_true",
                        help="Suppress per-token diagnostics; print only on leak.")
    args = parser.parse_args()

    sketch = Path(args.sketch)
    if not sketch.exists():
        print(f"ERROR: sketch not found: {sketch}", file=sys.stderr)
        return 2

    companion = Path(args.companion) if args.companion else None
    blocklist = Path(args.blocklist) if args.blocklist else None

    try:
        out = run_airlock(sketch, companion_path=companion,
                         blocklist_path=blocklist, quiet=args.quiet)
    except AirlockError as e:
        print(f"FAIL  {e}", file=sys.stderr)
        return 1

    if not args.quiet:
        print(
            f"PASS  airlock cleared "
            f"(txt_lines={out['txt_lines']} static={out['static_tokens']} "
            f"dynamic={out['dynamic_tokens']} companion={out['companion_present']})"
        )
    return 0


if __name__ == "__main__":
    sys.exit(_cli())
