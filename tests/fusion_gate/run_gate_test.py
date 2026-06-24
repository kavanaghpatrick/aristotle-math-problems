#!/usr/bin/env python3
"""Local test driver for the FUSION-lane gate — exercises
check_fusion_companion() and the airlock without hitting Aristotle.

Run:    python3 tests/fusion_gate/run_gate_test.py
Expect: PASS lines for all 5 test cases.

Cases:
  1. Valid bare .txt + valid .fusion.json companion          → PASS
  2. Bare .txt that LEAKS a strategy term ("Frey")           → REJECT (airlock)
  3. Companion with > 80 non-blank lines                     → REJECT (line budget)
  4. Bare .txt with NO companion file                        → REJECT (missing companion)
  5. Direct airlock-only call: leak detection without gate   → REJECT (AirlockError)

Reference:
  docs/fusion_axis_companion_spec.md
  docs/infrastructure_changes_may30/I8_fusion_lane.md
"""
import importlib.util
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
os.environ.setdefault("ARISTOTLE_API_KEY", "dummy-for-test")

# Load safe_aristotle_submit
spec = importlib.util.spec_from_file_location(
    "safe_aristotle_submit", str(ROOT / "scripts" / "safe_aristotle_submit.py")
)
sas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sas)

# Load airlock_check
spec_al = importlib.util.spec_from_file_location(
    "airlock_check", str(ROOT / "scripts" / "airlock_check.py")
)
al = importlib.util.module_from_spec(spec_al)
spec_al.loader.exec_module(al)

HERE = Path(__file__).resolve().parent
VALID = HERE / "sample_fusion.txt"
LEAKS = HERE / "sample_fusion_LEAKS.txt"
OVERSIZED = HERE / "sample_fusion_OVERSIZED.txt"
MISSING = HERE / "sample_fusion_MISSING.txt"

failures: list[str] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    if ok:
        print(f"PASS  {label}")
    else:
        print(f"FAIL  {label}  {detail}")
        failures.append(label)


# Case 1: valid bare + valid companion → PASS
try:
    out = sas.check_fusion_companion(VALID)
    check(
        "1. valid bare + valid companion passes",
        out["present"] is True
        and out["airlock_passed"] is True
        and out["non_blank_lines"] <= sas.FUSION_MAX_LINES
        and out["fusion"]["problem_id"] == "erdos_938"
        and 0.0 <= out["fusion"]["fit_score"] <= 1.0,
        detail=f"got {out}" if out else "no result",
    )
except sas.FusionCompanionError as e:
    check("1. valid bare + valid companion passes", False, str(e))

# Case 2: bare .txt LEAKS strategy term → REJECT (airlock)
try:
    sas.check_fusion_companion(LEAKS)
    check("2. leaking .txt rejected by airlock", False, "no error raised")
except sas.FusionCompanionError as e:
    msg = str(e)
    check(
        "2. leaking .txt rejected by airlock",
        "airlock REJECTED" in msg and ("frey" in msg.lower() or "Frey" in msg),
        detail=msg[:200],
    )

# Case 3: companion has > 80 non-blank lines → REJECT (line budget)
try:
    sas.check_fusion_companion(OVERSIZED)
    check("3. oversized companion rejected by line-budget", False, "no error raised")
except sas.FusionCompanionError as e:
    msg = str(e)
    check(
        "3. oversized companion rejected by line-budget",
        "non-blank lines" in msg and f"max {sas.FUSION_MAX_LINES}" in msg,
        detail=msg[:200],
    )

# Case 4: bare .txt has NO companion file → REJECT (missing)
try:
    sas.check_fusion_companion(MISSING)
    check("4. missing companion rejected", False, "no error raised")
except sas.FusionCompanionError as e:
    msg = str(e)
    check(
        "4. missing companion rejected",
        "FUSION lane requires a companion" in msg,
        detail=msg[:200],
    )

# Case 5: airlock-only call directly (regression — airlock works standalone)
try:
    al.run_airlock(LEAKS, quiet=True)
    check("5. airlock standalone detects leak", False, "no error raised")
except al.AirlockError as e:
    msg = str(e)
    check(
        "5. airlock standalone detects leak",
        "airlock REJECT" in msg and ("frey" in msg.lower() or "Frey" in msg),
        detail=msg[:200],
    )

if failures:
    print(f"\n{len(failures)} failure(s): {failures}")
    sys.exit(1)
print(f"\nAll fusion-gate tests passed ({5 - len(failures)}/5).")
