#!/usr/bin/env python3
"""
Strict audit of all 'compiled_clean' files in tracking.db.

COMPILED CLEAN means: 0 sorry, 0 axiom, file exists, no self-loops, no banned Finset.sym2.
Anything else gets downgraded.
"""

import os
import re
import sqlite3
from pathlib import Path

DB_PATH = "/Users/patrickkavanagh/math/submissions/tracking.db"
BASE_DIRS = [
    "/Users/patrickkavanagh/math/submissions/nu4_final",
    "/Users/patrickkavanagh/math/submissions",
    "/Users/patrickkavanagh/math",
]

def find_file(filename):
    """Try to locate a file across known directories."""
    for base in BASE_DIRS:
        path = os.path.join(base, filename)
        if os.path.isfile(path):
            return path
    # Also try stripping leading dirs from filename
    for base in BASE_DIRS:
        for root, dirs, files in os.walk(base):
            if os.path.basename(filename) in files:
                return os.path.join(root, os.path.basename(filename))
    return None

# F-mode post-audit detectors (S7, 2026-05-30 — failure_mode_prevention.md).
# These detect failure modes in Aristotle's output `.lean` files that compile
# cleanly but do NOT resolve the open gap. Each detector returns either None
# (no detection) or a (severity, message) tuple suitable for the issues list.

# F1 / F8 — Iff.rfl trap on undecidable wrappers.
# Pattern: `theorem foo : answer ↔ Statement := Iff.rfl` (or `:= by rfl`,
# `:= by bound`, `Eq.refl`).  Also catches the inverse shape where the
# definition is inlined: `theorem foo : <PRED> := Iff.rfl`.
F1_IFF_RFL_PATTERNS = [
    re.compile(r'theorem\s+\w+[^:]*:\s*\w+\s*↔.*?:=\s*Iff\.rfl\b'),
    re.compile(r'theorem\s+\w+[^:]*:\s*\w+\s*↔.*?:=\s*by\s+rfl\b'),
    re.compile(r'theorem\s+\w+[^:]*:\s*\w+\s*↔.*?:=\s*Eq\.refl\b'),
    re.compile(r'theorem\s+\w+[^:]*:\s*\w+\s*↔.*?:=\s*by\s+bound\b'),
]
# An `answer := <Expr>` definition followed by an iff theorem is the textbook
# F1/F8 pattern. If both appear in the file, we're highly confident.
F1_ANSWER_DEF = re.compile(r'^\s*(?:def|abbrev)\s+answer\s*[:=]', re.MULTILINE)

# F3 — side-lemma proliferation. Heuristic: ≥ N proven lemmas AND the main
# theorem (by name matching the file's problem id) is either absent or
# contains a sorry.
F3_LEMMA_THRESHOLD = 15

# F4 — axiomatize-the-hard. Aristotle leaves `exact?` as a trail when it
# failed to find a proof. exact? in a compiled file means the kernel
# silently accepted the auto-generated goal-closing tactic (or, worse, the
# tactic block was elided). Count occurrences.
#
# Note: `\b` does NOT match the boundary between `?` and whitespace because
# `?` is not a word character — both are non-word. We use a non-word
# look-behind (start-of-string or non-word char) plus a non-word look-ahead
# instead.
F4_EXACT_QUERY = re.compile(r'(?:^|\W)exact\?(?=\W|$)')
F4_APPLY_QUERY = re.compile(r'(?:^|\W)apply\?(?=\W|$)')
F4_REWRITE_QUERY = re.compile(r'(?:^|\W)(?:rewrite|rw)\?(?=\W|$)')

# F6 — restate-with-sorry. Aristotle prints a meta comment naming the
# failure ("Aristotle took a wrong turn", "Aristotle failed to find a proof")
# adjacent to a `:= by sorry`.
F6_META_FAILURE = re.compile(
    r'(?i)Aristotle\s+(?:took\s+a\s+wrong\s+turn|failed\s+to\s+find\s+a\s+proof|reason\s+code)'
)

# F9 — computational explosion / bounded native_decide leakage. When a
# theorem statement carries an explicit `n ≤ <literal>` or `n ∈ Finset.Icc`
# (the source conjecture didn't), it has been silently bounded. Combined
# with `native_decide`, this is F9.
# F9 — a theorem header that includes a numeric ceiling. We look for the
# `theorem` keyword followed (anywhere up to the `:=`) by one of the bounded
# patterns. We CANNOT use `[^:]*` because Lean uses `:` for type annotations
# inside argument lists `(n : ℕ)`. Use a non-greedy `.*?` instead, anchored
# at `:=`.
F9_BOUNDED_QUANT = re.compile(
    r'theorem\s+\w+.*?(?:≤\s*\d+|Finset\.Icc\s+\d+\s+\d+|Finset\.range\s+\d+).*?:=\s*by',
    re.DOTALL,
)
F9_NATIVE_DECIDE = re.compile(r'\bnative_decide\b')


def _detect_f1_iff_rfl(content: str, code_only: str) -> tuple[str, str] | None:
    """F1/F8 — Iff.rfl trap. Returns (severity, message) or None."""
    for pat in F1_IFF_RFL_PATTERNS:
        m = pat.search(code_only)
        if m:
            snippet = m.group(0)[:120]
            return ("CRITICAL",
                    f"F1/F8 Iff.rfl trap: theorem proven by definitional unfolding "
                    f"of `answer := <Statement>`. Does NOT resolve the open problem. "
                    f"Snippet: {snippet!r}")
    # Weaker signal: `def answer ...` plus any iff theorem in the file.
    if F1_ANSWER_DEF.search(code_only) and re.search(r'\bIff\.rfl\b|\bby\s+rfl\b', code_only):
        return ("CRITICAL",
                "F1/F8 Iff.rfl pattern: `answer := <expr>` definition AND `Iff.rfl`/`by rfl` "
                "tactic present in the same file. Highly likely to be a definitional tautology.")
    return None


def _detect_f3_side_lemmas(content: str, code_only: str, problem_id_hint: str = "") -> tuple[str, str] | None:
    """F3 — side-lemma proliferation without main target.

    Heuristic: count proven lemmas/theorems. If ≥ F3_LEMMA_THRESHOLD AND
    NO declaration name contains the problem-id hint, OR the file ends
    without the original target being closed, flag F3.

    Also catches files where the FIRST proven theorem matches the problem
    id (good) but later side-lemma growth dwarfs it (still F3).
    """
    blocks = re.split(r'(?=\b(?:theorem|lemma)\s)', code_only)
    proven_decls: list[str] = []
    for block in blocks:
        m = re.search(r'\b(theorem|lemma)\s+(\w+)', block)
        if m and not re.search(r'\bsorry\b', block):
            proven_decls.append(m.group(2))

    if len(proven_decls) < F3_LEMMA_THRESHOLD:
        return None

    # Did we close the main target? Heuristic: look for any declaration name
    # that matches the problem_id_hint (without `_` differences).
    if problem_id_hint:
        norm_pid = re.sub(r'[_\W]+', '', problem_id_hint).lower()
        names_norm = [re.sub(r'[_\W]+', '', n).lower() for n in proven_decls]
        if any(norm_pid in n for n in names_norm):
            return None  # main target appears closed — no F3

    # No problem-id hint OR no matching declaration → F3
    return ("HIGH",
            f"F3 side-lemma proliferation: {len(proven_decls)} proven lemmas/theorems "
            f"but no declaration matches problem_id '{problem_id_hint or '(none)'}'. "
            f"Likely infrastructure-without-target. First 5 names: {proven_decls[:5]}")


def _detect_f4_exact_query(content: str, code_only: str) -> tuple[str, str] | None:
    """F4 — exact? / apply? / rewrite? trails. Aristotle leaves these when
    it could not finish. Compiles only if they happen to succeed; otherwise
    indicates silent axiom-style leak.
    """
    exact_hits = F4_EXACT_QUERY.findall(code_only)
    apply_hits = F4_APPLY_QUERY.findall(code_only)
    rewrite_hits = F4_REWRITE_QUERY.findall(code_only)
    total = len(exact_hits) + len(apply_hits) + len(rewrite_hits)
    if total == 0:
        return None
    return ("HIGH",
            f"F4 exact?/apply?/rewrite? trail: "
            f"{len(exact_hits)} exact?, {len(apply_hits)} apply?, "
            f"{len(rewrite_hits)} rewrite?. Aristotle left auto-completion "
            f"placeholders. Audit each occurrence — they often hide F4 axiomatize-the-hard.")


def _detect_f6_restate_with_sorry(content: str, code_only: str) -> tuple[str, str] | None:
    """F6 — Aristotle meta-failure + sorry. Strong signal of restate-with-sorry.

    We use full `content` (with comments) for the meta-failure marker, since
    Aristotle's diagnostic is usually in a comment.
    """
    meta_match = F6_META_FAILURE.search(content)
    sorry_match = re.search(r'\bsorry\b', code_only)
    if meta_match and sorry_match:
        return ("CRITICAL",
                f"F6 restate-with-sorry: Aristotle meta-failure marker "
                f"('{meta_match.group(0)[:50]}') + sorry in same file. Target theorem "
                f"is not closed.")
    return None


def _detect_f9_bounded_dressed(content: str, code_only: str) -> tuple[str, str] | None:
    """F9 — bounded native_decide passed off as the unbounded conjecture."""
    bounded_match = F9_BOUNDED_QUANT.search(code_only)
    native_match = F9_NATIVE_DECIDE.search(code_only)
    if bounded_match and native_match:
        snippet = bounded_match.group(0)[:120]
        return ("HIGH",
                f"F9 bounded native_decide: theorem statement carries explicit "
                f"numeric ceiling AND uses native_decide. Likely silently narrowed "
                f"the original unbounded conjecture. Snippet: {snippet!r}")
    return None


def _extract_problem_id_from_filename(filename: str) -> str:
    """Extract a coarse problem-id hint from `slot697_erdos470_odd_weird.lean`-style names."""
    stem = Path(filename).stem
    # Strip slotNNN_ prefix and -output / -result suffixes
    stem = re.sub(r'^slot\d+_', '', stem)
    stem = re.sub(r'[-_]?(?:output|result|aristotle)$', '', stem)
    return stem


def detect_failure_modes(content: str, filename: str = "") -> list[tuple[str, str, str]]:
    """Run all F-mode detectors against `content`. Returns a list of
    (F-code, severity, message) tuples. Empty list = no detections.

    Public function — also used by tests in tests/test_failure_mode_detection.py.

    Args:
        content: full text of the Lean file.
        filename: optional filename for problem-id extraction (used by F3).
    """
    # Strip Lean comments for syntax-sensitive detectors. Block comments
    # `/- ... -/` and line comments `-- ...` are dropped.
    code_only = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
    code_only = re.sub(r'--.*$', '', code_only, flags=re.MULTILINE)

    pid_hint = _extract_problem_id_from_filename(filename) if filename else ""

    detections: list[tuple[str, str, str]] = []
    for code, detector in [
        ("F1", _detect_f1_iff_rfl),
        ("F3", lambda c, co: _detect_f3_side_lemmas(c, co, pid_hint)),
        ("F4", _detect_f4_exact_query),
        ("F6", _detect_f6_restate_with_sorry),
        ("F9", _detect_f9_bounded_dressed),
    ]:
        result = detector(content, code_only)
        if result is not None:
            severity, message = result
            detections.append((code, severity, message))
    return detections


def audit_file(filepath):
    """Audit a lean file for issues. Returns list of (severity, issue) tuples."""
    issues = []
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except:
        return [("CRITICAL", "Cannot read file")]

    # 1. Count actual sorry
    sorry_count = len(re.findall(r'\bsorry\b', content))
    if sorry_count > 0:
        issues.append(("CRITICAL", f"Contains {sorry_count} sorry"))

    # 2. Check for axiom declarations
    axioms = re.findall(r'^axiom\s+(\w+)', content, re.MULTILINE)
    if axioms:
        issues.append(("CRITICAL", f"Contains axioms: {', '.join(axioms)}"))

    # 3. Check for self-loops: Sym2.mk(x, x) patterns
    # Match Sym2.mk (x, x) or Sym2.mk (x , x)
    self_loops_sym2mk = re.findall(r'Sym2\.mk\s*\(\s*(\w+)\s*,\s*\1\s*\)', content)
    if self_loops_sym2mk:
        issues.append(("CRITICAL", f"Self-loops via Sym2.mk: {self_loops_sym2mk[:3]}"))

    # Match s(x, x) patterns in non-comment lines
    lines = content.split('\n')
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('--') or stripped.startswith('/-'):
            continue
        s_self_loops = re.findall(r's\((\w+),\s*\1\)', line)
        if s_self_loops:
            issues.append(("CRITICAL", f"Self-loop s({s_self_loops[0]},{s_self_loops[0]}) at line {i+1}"))
            break  # One is enough

    # 4. Check for Finset.sym2 usage (banned for edge enumeration)
    sym2_uses = re.findall(r'Finset\.sym2|\.sym2\b', content)
    # Exclude comments
    code_only = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
    code_only = re.sub(r'--.*$', '', code_only, flags=re.MULTILINE)
    sym2_code_uses = re.findall(r'(?:Finset\.sym2|\.sym2\b)', code_only)
    if sym2_code_uses:
        issues.append(("HIGH", f"Uses Finset.sym2 ({len(sym2_code_uses)} times) - includes self-loops"))

    # 4b. em-tautology pattern (added 2026-05-28 from PILOT_ERDOS850).
    # Aristotle proves goals of the form `P ∨ ¬P` with `exact em _` — file compiles
    # cleanly but resolves nothing. Detect by looking for both the disjunction shape
    # in a theorem statement AND an em/Classical.em proof tactic.
    em_proof_pattern = re.compile(r'\b(?:exact\s+em\b|Classical\.em\b|Decidable\.em\b|by\s+exact\s+em)')
    has_em_proof = bool(em_proof_pattern.search(code_only))
    theorem_match = re.search(r'theorem\s+\w+[^:]*:(.*?):=\s*by\b', code_only, re.DOTALL)
    has_em_goal = False
    if theorem_match:
        body = re.sub(r'\s+', ' ', theorem_match.group(1)).strip()
        parts = re.split(r'∨\s*¬', body, maxsplit=1)
        if len(parts) == 2:
            norm = lambda s: re.sub(r'[\s()]+', '', s)
            if norm(parts[0]) == norm(parts[1]) and norm(parts[0]):
                has_em_goal = True
    if has_em_proof and has_em_goal:
        issues.append(("CRITICAL", "em-tautology: goal is P∨¬P, proof is em — does NOT resolve open problem"))
    elif has_em_goal:
        # Goal is a tautology even if proof shape differs — still pathological
        issues.append(("CRITICAL", "em-tautology shape: goal is P∨¬P (excluded middle) — does NOT resolve open problem"))

    # 5. Count proven lemmas/theorems (for accurate proven_count)
    blocks = re.split(r'(?=\b(?:theorem|lemma)\s)', content)
    proven = 0
    for block in blocks:
        if re.search(r'\b(theorem|lemma)\s+\w+', block):
            if not re.search(r'\bsorry\b', block):
                proven += 1

    # 6. F-mode detectors (S7, 2026-05-30). Each detector that fires appends
    # an (severity, message) entry to issues. The detectors look for shapes
    # that compile cleanly but do NOT resolve the open gap.
    f_mode_detections = detect_failure_modes(content, filename=str(filepath))
    for code, severity, message in f_mode_detections:
        issues.append((severity, f"{code}: {message}"))

    return issues, sorry_count, proven

def main():
    conn = sqlite3.connect(DB_PATH)

    # Schema-honesty (2026-05-28): status vocabulary is now
    # {submitted, compile_failed, compiled_partial, compiled_no_advance, compiled_advance, disproven}.
    # The historical 'compiled_clean'/'proven' bucket collapsed into 'compiled_no_advance'.
    # status_legacy preserves the pre-migration label.
    # We re-audit any row whose new status claims a compile (partial or no_advance) — these
    # are the candidates that might be axiomatizing prior work or hiding a sorry.
    # NOTE: this script never SETS status='compiled_advance'. That bucket is opt-in and
    # requires target_resolved=1 + axiomatizes_prior_work=0 + contribution_statement NOT NULL.
    rows = conn.execute("""
        SELECT id, filename, sorry_count, proven_count, status, verified, notes
        FROM submissions
        WHERE status IN ('compiled_no_advance', 'compiled_partial')
    """).fetchall()

    print(f"Auditing {len(rows)} files marked as compiled clean...\n")

    stats = {
        "clean": 0,
        "downgraded_sorry": 0,
        "downgraded_axiom": 0,
        "downgraded_self_loop": 0,
        "downgraded_missing": 0,
        "flagged_sym2": 0,
    }

    clean_files = []
    problematic_files = []

    for row_id, filename, db_sorry, db_proven, status, verified, notes in rows:
        filepath = find_file(filename)

        if not filepath:
            # File doesn't exist — in the new vocab, that's compile_failed
            print(f"  MISSING: {filename} -> downgrade to 'compile_failed'")
            conn.execute(
                "UPDATE submissions SET status='compile_failed', verified=0, notes=COALESCE(notes,'') || ' [AUDIT: file not found on disk]' WHERE id=?",
                (row_id,)
            )
            stats["downgraded_missing"] += 1
            problematic_files.append((filename, "compile_failed", "File not found on disk"))
            continue

        if not filename.endswith('.lean'):
            # Non-lean files (like .md) - can't be "proven"
            print(f"  NON-LEAN: {filename} -> downgrade to 'compile_failed'")
            conn.execute(
                "UPDATE submissions SET status='compile_failed', verified=0, notes=COALESCE(notes,'') || ' [AUDIT: not a lean file]' WHERE id=?",
                (row_id,)
            )
            stats["downgraded_sorry"] += 1
            continue

        result = audit_file(filepath)
        if isinstance(result, list):
            # Error reading file
            issues = result
            actual_sorry = None
            actual_proven = None
        else:
            issues, actual_sorry, actual_proven = result

        critical_issues = [i for i in issues if i[0] == "CRITICAL"]
        high_issues = [i for i in issues if i[0] == "HIGH"]

        # Schema-honesty: extract axiom count and axiomatizes_prior_work for every file we audit,
        # regardless of issue classification. These are written to the new honesty columns.
        try:
            file_text = Path(filepath).read_text()
            axiom_matches = re.findall(r'^\s*axiom\s+(\w+)', file_text, re.MULTILINE)
            axiom_count = len(axiom_matches)
        except Exception:
            axiom_count = None
        axiomatizes_prior_work = 1 if (axiom_count or 0) > 0 else 0

        if critical_issues:
            # Downgrade — but everything downgrades to compiled_partial or compiled_no_advance
            # in the new vocabulary. We NEVER set compiled_advance from this script.
            issue_strs = "; ".join(f"{sev}: {desc}" for sev, desc in critical_issues)
            new_notes = f"[AUDIT DOWNGRADED: {issue_strs}]"

            # Determine new status (new vocabulary only)
            if any("sorry" in i[1].lower() for i in critical_issues):
                # File has sorry → it's at most compiled_partial
                new_status = "compiled_partial"
                stats["downgraded_sorry"] += 1
            elif any("axiom" in i[1].lower() for i in critical_issues):
                # File compiles, but axiomatizes prior work → compiled_no_advance, not _advance.
                new_status = "compiled_no_advance"
                stats["downgraded_axiom"] += 1
            elif any("self-loop" in i[1].lower() or "Self-loop" in i[1] for i in critical_issues):
                new_status = "compiled_partial"
                stats["downgraded_self_loop"] += 1
            else:
                new_status = "compiled_no_advance"
                stats["downgraded_sorry"] += 1

            print(f"  DOWNGRADE: {filename} -> '{new_status}' (axiom={axiom_count}) ({issue_strs})")
            conn.execute("""
                UPDATE submissions SET
                    status=?,
                    verified=0,
                    sorry_count=COALESCE(?, sorry_count),
                    proven_count=COALESCE(?, proven_count),
                    axiom_count=COALESCE(?, axiom_count),
                    axiomatizes_prior_work=?,
                    notes=CASE WHEN notes IS NULL THEN ? ELSE notes || ' ' || ? END
                WHERE id=?
            """, (new_status, actual_sorry, actual_proven, axiom_count,
                  axiomatizes_prior_work, new_notes, new_notes, row_id))
            problematic_files.append((filename, new_status, issue_strs))

        elif high_issues:
            # Flag but don't downgrade further; record axiom info.
            issue_strs = "; ".join(f"{sev}: {desc}" for sev, desc in high_issues)
            flag_note = f"[AUDIT WARNING: {issue_strs}]"
            print(f"  WARNING: {filename} (axiom={axiom_count}) ({issue_strs})")
            conn.execute("""
                UPDATE submissions SET
                    notes=CASE WHEN notes IS NULL THEN ? ELSE notes || ' ' || ? END,
                    sorry_count=COALESCE(?, sorry_count),
                    proven_count=COALESCE(?, proven_count),
                    axiom_count=COALESCE(?, axiom_count),
                    axiomatizes_prior_work=?
                WHERE id=?
            """, (flag_note, flag_note, actual_sorry, actual_proven,
                  axiom_count, axiomatizes_prior_work, row_id))
            stats["flagged_sym2"] += 1
            clean_files.append((filename, f"FLAGGED: {issue_strs}"))

        else:
            # No critical issues. Record axiom info but DO NOT auto-promote to compiled_advance —
            # that requires target_resolved=1 AND contribution_statement set manually.
            verdict = "compiled_no_advance" if axiom_count and axiom_count > 0 else "compiled_no_advance"
            note = f"[AUDIT: axiom_count={axiom_count}]" if axiom_count is not None else ""
            print(f"  CLEAN-COMPILE: {filename} (axiom={axiom_count})")
            conn.execute("""
                UPDATE submissions SET
                    sorry_count=COALESCE(?, sorry_count),
                    proven_count=COALESCE(?, proven_count),
                    axiom_count=COALESCE(?, axiom_count),
                    axiomatizes_prior_work=?,
                    verified=1,
                    notes=CASE WHEN ? = '' THEN notes ELSE COALESCE(notes,'') || ' ' || ? END
                WHERE id=?
            """, (actual_sorry, actual_proven, axiom_count, axiomatizes_prior_work,
                  note, note, row_id))
            stats["clean"] += 1
            tag = "CLEAN" if not axiomatizes_prior_work else f"CLEAN-axioms={axiom_count}"
            clean_files.append((filename, tag))

    conn.commit()

    # Print summary
    print(f"\n{'='*60}")
    print("AUDIT SUMMARY")
    print(f"{'='*60}")
    print(f"Total files audited:        {len(rows)}")
    print(f"Truly CLEAN (compiled):     {stats['clean']}")
    print(f"Flagged (sym2 warning):     {stats['flagged_sym2']}")
    print(f"Downgraded (has sorry):     {stats['downgraded_sorry']}")
    print(f"Downgraded (has axiom):     {stats['downgraded_axiom']}")
    print(f"Downgraded (self-loops):    {stats['downgraded_self_loop']}")
    print(f"Downgraded (file missing):  {stats['downgraded_missing']}")
    print(f"\n{'='*60}")
    print("COMPILED CLEAN FILES (verified=1, 0 sorry, 0 axiom, no self-loops):")
    print(f"{'='*60}")
    for fname, note in sorted(clean_files):
        marker = "  " if note == "CLEAN" else "⚠ "
        print(f"  {marker}{fname} {'(' + note + ')' if note != 'CLEAN' else ''}")

    print(f"\n{'='*60}")
    print("DOWNGRADED FILES:")
    print(f"{'='*60}")
    for fname, new_status, reason in sorted(problematic_files):
        print(f"  {fname} -> {new_status}: {reason}")

    # Final count (new vocabulary)
    final_compile_ok = conn.execute(
        "SELECT COUNT(*) FROM submissions WHERE status='compiled_no_advance' AND verified = 1"
    ).fetchone()[0]
    final_axiomatized = conn.execute(
        "SELECT COUNT(*) FROM submissions WHERE status='compiled_no_advance' AND axiomatizes_prior_work=1"
    ).fetchone()[0]
    final_advance = conn.execute(
        "SELECT COUNT(*) FROM submissions WHERE status='compiled_advance'"
    ).fetchone()[0]
    print(f"\nFinal counts (new vocabulary):")
    print(f"  compiled_no_advance (verified):   {final_compile_ok}")
    print(f"     of which axiomatize prior work: {final_axiomatized}")
    print(f"  compiled_advance:                  {final_advance}  (only /audit + contribution_statement can promote here)")

    conn.close()

if __name__ == '__main__':
    main()
