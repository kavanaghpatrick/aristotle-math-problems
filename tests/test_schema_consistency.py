"""Regression test: every code reference to submissions.status uses a status
that actually exists in the DB (or in the canonical enum).

Background
----------

On 2026-05-28 the `submissions.status` vocabulary was renamed. The old
buckets {`compiled_clean`, `near_miss`, `completed`, `failed`, `running`,
`pending`, `validated`, `draft`} were collapsed into the canonical six:

  submitted | compile_failed | compiled_partial | compiled_no_advance
  | compiled_advance | disproven

The rename SET DB rows but did NOT update every code path that filtered
on the old vocab. The result: `safe_aristotle_submit.py:gather_context()`
filtered `status IN ('compiled_clean','near_miss','completed')` and
silently returned 0 rows for an unknown stretch of submissions — auto-
context was broken without anyone noticing because there was no test that
asserted code references match DB reality.

This test prevents the next rename from doing the same.

What it checks
--------------

1. Every code-file (Python, shell, markdown command, .bats) is grepped
   for status literals near the token `status`.
2. The DB's distinct `submissions.status` values are loaded.
3. We assert each code-side literal is either:
     a. in the DB
     b. in the canonical enum (a status that is valid but happens to
        have zero rows right now)
     c. in `KNOWN_HISTORICAL` — explicitly grandfathered references
        inside migration scripts / one-shot backfills / documentation.

Adding a new status
-------------------

When introducing a new canonical status:
  1. Update CANONICAL_STATUSES below.
  2. Update CLAUDE.md and docs/infrastructure_changes_*/I3_skill_audit.md.
  3. Migrate existing rows BEFORE writing code that filters on the new
     status (otherwise this test will pass but auto-context will silently
     break for any problem whose only artifacts pre-date the migration).

Retiring a status
-----------------

When removing a canonical status:
  1. Migrate all DB rows away from it first.
  2. Remove ALL code references (this test will fail until they are gone
     or moved into KNOWN_HISTORICAL).
  3. Update CANONICAL_STATUSES.
"""

from __future__ import annotations

import re
import sqlite3
from pathlib import Path
from typing import Iterable

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent
DB_PATH = REPO_ROOT / "submissions" / "tracking.db"


# Canonical submissions.status enum as of 2026-05-28.
# Mirror this in CLAUDE.md and docs/infrastructure_changes_may30/I3_skill_audit.md.
CANONICAL_STATUSES: set[str] = {
    "submitted",
    "compile_failed",
    "compiled_partial",
    "compiled_no_advance",
    "compiled_advance",
    "disproven",
}


# References that are known to mention dead status names but should NOT trip
# the test because they live in clearly historical/transitional contexts.
#
# Each entry is (path_suffix, literal). path_suffix matches by `str.endswith`.
KNOWN_HISTORICAL: set[tuple[str, str]] = {
    # migrate_honest_labels.py is the one-shot migration that wrote the
    # new vocab — it MUST reference the old vocab in its WHERE clause.
    ("scripts/migrate_honest_labels.py", "compiled_clean"),
    ("scripts/migrate_honest_labels.py", "proven"),
    ("scripts/migrate_honest_labels.py", "PROVEN"),
    # audit_proven.py has an inline note explaining the rename — the
    # literals appear inside a docstring/comment block.
    ("scripts/audit_proven.py", "compiled_clean"),
    ("scripts/audit_proven.py", "proven"),
    # safe_aristotle_submit.py comments reference the old vocab to explain
    # the pre-2026-05-30 bug.
    ("scripts/safe_aristotle_submit.py", "compiled_clean"),
    ("scripts/safe_aristotle_submit.py", "near_miss"),
    ("scripts/safe_aristotle_submit.py", "completed"),
}


# Files we never scan.
EXCLUDED_DIRS: set[str] = {
    "__pycache__",
    ".git",
    "node_modules",
    "build",
    "target",
    ".venv",
    "venv",
    "specs",   # spec docs intentionally describe historical states
    "analysis",  # analysis notes record historical broken queries
    "docs",    # docs may describe the rename itself
    "ai",      # ai/tasks/spec/* are historical design docs
    "archive", # explicitly archived old code
    ".lake",   # mathlib upstream
    ".claude/worktrees",
    "problem-databases",  # uses its own `problems.status` vocabulary
    "formal-conjectures",  # upstream import, not our code
}


# File extensions to scan.
SCANNED_EXTENSIONS: set[str] = {".py", ".sh", ".md", ".bats"}


# Pattern: a SQL string literal preceded by a `status` keyword (case-insensitive).
# We deliberately match BOTH ASCII single-quoted and double-quoted forms.
#
# Matches things like:
#   status = 'compiled_clean'
#   status IN ('compiled_clean','near_miss')
#   "status='completed'"
#   WHERE s.status = 'proven'
#
# Does NOT match:
#   status = ProjectStatus.RUNNING       (no quotes; Aristotle's enum)
#   "submissions.status"                 (no value literal)
STATUS_LITERAL_RE = re.compile(
    r"""
    \b(?:submissions\.)?status\b   # 'status' or 'submissions.status'
    \s*(?:=|==|IN|in|!=|<>)\s*     # comparison op
    \(?                            # optional opening paren for IN (...)
    (?P<literals>[^;)]*?)          # everything up to ; or )
    (?:\)|;|\Z|--|--|\n)           # terminator
    """,
    re.VERBOSE,
)


# Pattern: any single- or double-quoted bareword that could plausibly be a
# status. We then filter to "looks status-like" words to cut noise.
QUOTED_TOKEN_RE = re.compile(r"""['"]([a-z_][a-z0-9_]{2,30})['"]""", re.IGNORECASE)


# Words that look like statuses but are not — must NOT be treated as candidates.
# These commonly appear quoted near the word `status` for unrelated reasons.
NOT_STATUS_TOKENS: set[str] = {
    # Aristotle's TaskStatus enum
    "RUNNING", "IDLE", "UNKNOWN", "COMPLETE", "COMPLETE_WITH_ERRORS",
    "QUEUED", "IN_PROGRESS", "FAILED", "CANCELED", "OUT_OF_BUDGET",
    "ERROR", "running", "idle", "unknown", "complete",
    # SQL keywords
    "AND", "OR", "NULL", "IS", "NOT",
    # Generic dict keys / JSON keys (submission_queue.py uses these as
    # queue-bucket names, not DB statuses)
    "pending", "active", "history",
    # Common substrings that aren't status
    "INTEGER", "TEXT", "REAL", "DEFAULT", "PRIMARY", "KEY",
    "status",  # the column name itself, when quoted
    "uuid", "filename", "problem_id", "output_file",
    # Verdict tokens in analysis/output formatting (not DB values)
    "success", "partial", "negated", "syntax_error", "incomplete",
    "RESOLVED", "PARTIAL", "INFRA", "INFRASTRUCTURE",
    "PROVEN", "NEAR_MISS", "NEEDS_WORK", "INVALID",
    "COMPILED_NO_ADVANCE", "COMPILED_ADVANCE", "COMPILED_PARTIAL",
    "COMPILE_FAILED", "DISPROVEN", "SUBMITTED",
}


def _iter_code_files() -> Iterable[Path]:
    for path in REPO_ROOT.rglob("*"):
        if not path.is_file():
            continue
        if path.suffix not in SCANNED_EXTENSIONS:
            continue
        rel = path.relative_to(REPO_ROOT)
        parts = set(rel.parts)
        if parts & EXCLUDED_DIRS:
            continue
        # Skip the migration script — it MUST reference dead vocab.
        # We allow specific tokens via KNOWN_HISTORICAL.
        yield path


_OTHER_TABLES = (
    "literature_lemmas", "findings", "problems", "proof_queue",
    "codex_proofs", "false_lemmas", "nu4_cases", "generator_tasks",
    "efu", "proven_theorems", "erdos", "metadata",
)


def _is_submissions_context(text: str, pos: int) -> bool:
    """Heuristic: is this `status` literal referring to submissions.status?

    Algorithm: scan backwards from `pos` up to 600 chars or to the previous
    semicolon/SQL-statement-boundary, find the most recent `FROM <table>` or
    `UPDATE <table>` clause, and check whether `<table>` is `submissions`.

    Falls back to: if no FROM/UPDATE is found in scope, accept iff the line
    references `submissions` directly (e.g., a Python variable like
    `submissions_status` would NOT be caught because the regex only matches
    bare `status`).
    """
    # Find the START of the current SQL-ish statement.
    # Boundaries: triple-quote, function def, line "execute(" etc.
    # Cheap: scan back to most recent ';' or '"""' or string start.
    start = pos
    for boundary in (";", '"""', "'''", "execute(", "execute (",
                     "UPDATE ", "INSERT ", "SELECT ", "WHERE "):
        last = text.rfind(boundary, max(0, pos - 1000), pos)
        if last > start - 1000:
            start = max(start, last - 200)  # back off slightly to catch FROM
    start = max(0, start)
    window = text[start : pos + 50]

    # Look for FROM <table> or UPDATE <table> in scope.
    last_from = None
    last_update = None
    for m in re.finditer(
        r"""(?ix)
        \b(?:FROM|UPDATE|INTO)\s+
        ([a-z_][a-z0-9_]*)
        (?:\s+(?:AS\s+)?[a-z_][a-z0-9_]*)?
        """,
        window,
    ):
        table = m.group(1).lower()
        if m.group(0).upper().startswith("FROM"):
            last_from = table
        else:
            last_update = table

    # If we found an UPDATE in scope, it overrides FROM.
    table_in_scope = last_update or last_from

    if table_in_scope == "submissions":
        return True
    if table_in_scope in _OTHER_TABLES:
        return False
    # No table identified — fall back to file-level heuristic.
    immediate = text[max(0, pos - 200) : pos + 80]
    if any(other in immediate for other in _OTHER_TABLES):
        return False
    if "submissions" in immediate:
        return True
    return False


def _extract_status_literals(text: str) -> set[str]:
    """Return the set of all distinct string literals that appear in a
    `submissions.status <op> 'X'` clause.

    We use a TIGHT regex that requires the literal to be the immediate
    operand of a comparison to `status`, AND we further filter to contexts
    that are clearly about submissions.status (not literature_lemmas.proof_status,
    not problems.status, not findings.status).
    """
    found: set[str] = set()

    # Pattern 1: `status <op> 'X'` (with optional alias prefix like `s.status`).
    # We deliberately do NOT match `proof_status` or any *_status name — only
    # the bare `status` column.
    pattern1 = re.compile(
        r"""(?ix)
        (?<!_)                              # not preceded by underscore (so proof_status doesn't match)
        \b(?:[a-z_][a-z0-9_]*\.)?status\b
        \s*(?:=|==|!=|<>)\s*
        ['"]([a-z_][a-z0-9_]{1,40})['"]
        """
    )
    for m in pattern1.finditer(text):
        if not _is_submissions_context(text, m.start()):
            continue
        tok = m.group(1)
        if tok not in NOT_STATUS_TOKENS:
            found.add(tok)

    # Pattern 2: `status IN ('X', 'Y', ...)` or `NOT IN`.
    pattern2 = re.compile(
        r"""(?ix)
        (?<!_)
        \b(?:[a-z_][a-z0-9_]*\.)?status\b
        \s+(?:NOT\s+)?IN\s*\(
        ([^)]+)
        \)
        """
    )
    for m in pattern2.finditer(text):
        if not _is_submissions_context(text, m.start()):
            continue
        list_text = m.group(1)
        for tm in re.finditer(r"""['"]([a-z_][a-z0-9_]{1,40})['"]""", list_text):
            tok = tm.group(1)
            if tok not in NOT_STATUS_TOKENS:
                found.add(tok)

    return found


def _db_statuses() -> set[str]:
    if not DB_PATH.exists():
        pytest.skip(f"tracking.db not found at {DB_PATH}")
    conn = sqlite3.connect(str(DB_PATH))
    try:
        rows = conn.execute(
            "SELECT DISTINCT status FROM submissions WHERE status IS NOT NULL"
        ).fetchall()
        return {row[0] for row in rows}
    finally:
        conn.close()


def test_canonical_matches_db():
    """The DB should only contain canonical statuses (no rot the other way)."""
    db = _db_statuses()
    # Some legacy rows may still be empty-status; ignore None.
    extra = db - CANONICAL_STATUSES
    assert not extra, (
        f"DB contains non-canonical statuses {sorted(extra)}.\n"
        f"Either migrate them or update CANONICAL_STATUSES in {__file__}."
    )


def test_no_dead_code_status_references():
    """Every code-side `status = 'X'` literal must be canonical (or
    grandfathered)."""
    offenders: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()  # (relpath, literal) pairs already reported

    for path in _iter_code_files():
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        literals = _extract_status_literals(text)
        if not literals:
            continue
        rel = str(path.relative_to(REPO_ROOT))
        for lit in literals:
            if lit in CANONICAL_STATUSES:
                continue
            key = (rel, lit)
            if key in seen:
                continue
            seen.add(key)
            # Allow known historical references.
            grandfathered = any(
                rel.endswith(suffix) and lit == hist_lit
                for suffix, hist_lit in KNOWN_HISTORICAL
            )
            if grandfathered:
                continue
            offenders.append((rel, lit))

    if offenders:
        msg = "Dead status references found:\n" + "\n".join(
            f"  {p}: '{lit}'" for p, lit in offenders
        )
        msg += (
            "\n\nFix by replacing each with a value from CANONICAL_STATUSES "
            f"{sorted(CANONICAL_STATUSES)}, or grandfather it by adding "
            "(path_suffix, literal) to KNOWN_HISTORICAL in this test."
        )
        raise AssertionError(msg)


def test_canonical_documented_in_claude_md():
    """The canonical enum must appear in CLAUDE.md so reviewers can find
    the source of truth without grepping."""
    claude_md = REPO_ROOT / "CLAUDE.md"
    if not claude_md.exists():
        pytest.skip("CLAUDE.md missing")
    text = claude_md.read_text(encoding="utf-8", errors="ignore")
    missing = [s for s in CANONICAL_STATUSES if s not in text]
    assert not missing, (
        f"CLAUDE.md does not mention canonical status(es): {sorted(missing)}.\n"
        "Add them so future maintainers know the schema."
    )


if __name__ == "__main__":
    # Allow `python3 tests/test_schema_consistency.py` to print a report.
    db = _db_statuses()
    print(f"DB has {len(db)} distinct statuses: {sorted(db)}")
    code_lits: dict[str, set[str]] = {}
    for path in _iter_code_files():
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        lits = _extract_status_literals(text)
        if lits:
            code_lits[str(path.relative_to(REPO_ROOT))] = lits
    all_code = set().union(*code_lits.values()) if code_lits else set()
    print(f"Code references {len(all_code)} distinct statuses: {sorted(all_code)}")
    dead = all_code - CANONICAL_STATUSES
    print(f"Dead (non-canonical) code references: {sorted(dead)}")
    for path, lits in sorted(code_lits.items()):
        dead_in_file = lits - CANONICAL_STATUSES
        if dead_in_file:
            grandfathered = []
            for lit in dead_in_file:
                if any(path.endswith(s) and lit == h for s, h in KNOWN_HISTORICAL):
                    grandfathered.append(lit)
            real_dead = dead_in_file - set(grandfathered)
            if real_dead:
                print(f"  {path}: {sorted(real_dead)}")
