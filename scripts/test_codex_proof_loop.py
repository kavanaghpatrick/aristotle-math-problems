#!/usr/bin/env python3
"""Unit tests for codex_proof_loop.py pure functions."""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

# Import functions directly by executing the module up to __main__
_code = open(os.path.join(os.path.dirname(__file__), "codex_proof_loop.py")).read()
_code = _code.split("if __name__")[0]
exec(compile(_code, "codex_proof_loop.py", "exec"))

passed = 0
failed = 0

def check(name, condition):
    global passed, failed
    if condition:
        print(f"  PASS: {name}")
        passed += 1
    else:
        print(f"  FAIL: {name}")
        failed += 1


# ── count_sorries ──────────────────────────────────────────────────────────
print("\n=== count_sorries ===")

check("clean code = 0", count_sorries("import Mathlib\n\ntheorem foo : 1 = 1 := by rfl") == 0)
check("one sorry", count_sorries("theorem foo : 1 = 1 := by sorry") == 1)
check("two sorries", count_sorries("theorem foo : 1 = 1 := by sorry\nlemma bar : 2 = 2 := by sorry") == 2)
check("line comment not counted", count_sorries("-- sorry\ntheorem foo : 1 = 1 := by rfl") == 0)
check("inline comment not counted", count_sorries("theorem foo : 1 = 1 := by rfl -- sorry") == 0)
check("block comment not counted", count_sorries("/- sorry -/\ntheorem foo : 1 = 1 := by rfl") == 0)
check("sorry in identifier not counted", count_sorries("def notsorry := 1") == 0)
check("sorry at end of tactic", count_sorries("  exact sorry") == 1)


# ── extract_theorem_statement ──────────────────────────────────────────────
print("\n=== extract_theorem_statement ===")

check("single theorem", extract_theorem_statement(
    "import Mathlib\n\ntheorem foo (n : Nat) : n = n := by rfl"
) == "theorem foo (n : Nat) : n = n")

check("multi-line theorem", extract_theorem_statement(
    "theorem bar\n    (n : Nat)\n    : n = n := by rfl"
) is not None)

check("lemma", extract_theorem_statement(
    "lemma baz : True := trivial"
) is not None)

check("no theorem returns None", extract_theorem_statement(
    "import Mathlib\ndef foo := 1"
) is None)


# ── check_statement_locked ─────────────────────────────────────────────────
print("\n=== check_statement_locked ===")

check("exact match", check_statement_locked(
    "theorem foo : 1 = 1", "theorem foo : 1 = 1"
))
check("whitespace difference OK", check_statement_locked(
    "theorem foo  :  1 = 1", "theorem foo : 1 = 1"
))
check("changed statement rejected", not check_statement_locked(
    "theorem foo : 1 = 1", "theorem foo : 2 = 2"
))


# ── select_best ────────────────────────────────────────────────────────────
print("\n=== select_best ===")

it1 = IterationResult(1, "code1", False, "err", 3, 10.0)
it2 = IterationResult(2, "code2", True, "", 1, 15.0)
it3 = IterationResult(3, "code3", True, "", 2, 12.0)
it4 = IterationResult(4, "code4", False, "err", 1, 8.0)

check("empty list returns None", select_best([]) is None)
check("one compiled picks it", select_best([it1, it2]).iteration == 2)
check("compiled beats fewer sorries uncompiled", select_best([it4, it2]).iteration == 2)
check("fewer sorries among compiled", select_best([it2, it3]).iteration == 2)
check("all fail picks fewest sorries", select_best([it1, it4]).iteration == 4)

# Tie-breaking: same sorry count, compiled, later iteration wins
it5 = IterationResult(5, "code5", True, "", 1, 10.0)
check("tie-break: later iteration", select_best([it2, it5]).iteration == 5)


# ── extract_lean_from_output ───────────────────────────────────────────────
print("\n=== extract_lean_from_output ===")

check("raw lean passthrough", extract_lean_from_output(
    "import Mathlib\n\ntheorem foo := sorry"
).startswith("import"))

check("markdown fence extraction", extract_lean_from_output(
    "Here's the proof:\n```lean\nimport Mathlib\ntheorem foo := sorry\n```\nDone."
).startswith("import"))

check("generic fence extraction", extract_lean_from_output(
    "```\nimport Mathlib\ntheorem foo := sorry\n```"
).startswith("import"))


# ── derive_problem_id ──────────────────────────────────────────────────────
print("\n=== derive_problem_id ===")

check("slug from text", derive_problem_id("Prove Erdos 850 conjecture") == "prove_erdos_850_conjecture")
check("short text", derive_problem_id("foo") == "foo")


# ── Summary ────────────────────────────────────────────────────────────────
print(f"\n{'='*40}")
print(f"  {passed} passed, {failed} failed")
print(f"{'='*40}")

sys.exit(1 if failed else 0)
