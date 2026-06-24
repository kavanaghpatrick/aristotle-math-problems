#!/usr/bin/env python3
"""Local test driver for check_closure_axis() — exercises gate decisions without
hitting the Aristotle API.

Run: python3 tests/closure_gate/run_gate_test.py
Expected: prints PASS for all 6 cases.
"""
import importlib.util
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
os.environ.setdefault("ARISTOTLE_API_KEY", "dummy-for-test")

spec = importlib.util.spec_from_file_location(
    "safe_aristotle_submit", str(ROOT / "scripts" / "safe_aristotle_submit.py")
)
sas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sas)

HERE = Path(__file__).resolve().parent
BOUNDED = HERE / "sample_bounded.txt"
REAL = HERE / "sample_real.txt"
MISSING = HERE / "sample_missing.txt"

failures = []


def check(label: str, ok: bool, detail: str = ""):
    if ok:
        print(f"PASS  {label}")
    else:
        print(f"FAIL  {label}  {detail}")
        failures.append(label)


# 1) real_closure_candidate=true → passes without flag
try:
    out = sas.check_closure_axis(REAL, rubric_points=False)
    check("real-candidate without flag passes",
          out["present"] and out["real_closure_candidate"] is True and not out["override"])
except sas.ClosureAxisError as e:
    check("real-candidate without flag passes", False, str(e))

# 2) real_closure_candidate=false without --rubric-points → REJECTS
try:
    sas.check_closure_axis(BOUNDED, rubric_points=False)
    check("bounded-version without --rubric-points rejects", False, "no error raised")
except sas.ClosureAxisError as e:
    msg = str(e)
    check("bounded-version without --rubric-points rejects",
          "real_closure_candidate=false" in msg and "--rubric-points" in msg)

# 3) real_closure_candidate=false with --rubric-points → PASSES + override=True
try:
    out = sas.check_closure_axis(BOUNDED, rubric_points=True)
    check("bounded-version with --rubric-points passes",
          out["present"] and out["real_closure_candidate"] is False and out["override"] is True)
except sas.ClosureAxisError as e:
    check("bounded-version with --rubric-points passes", False, str(e))

# 4) missing companion file → WARN + allow
try:
    out = sas.check_closure_axis(MISSING, rubric_points=False)
    check("missing companion allowed with warn",
          out["present"] is False and out["axis"] is None and out["override"] is False)
except sas.ClosureAxisError as e:
    check("missing companion allowed with warn", False, str(e))

# 5) bad enum value → REJECTS
bad_path = HERE / "bad_enum.txt"
bad_path.write_text("OPEN GAP: bad enum test\n\ntheorem foo : True := by sorry\n")
bad_companion = bad_path.with_suffix(".closure.json")
bad_companion.write_text(json.dumps({
    "CS": "NOT_A_VALID_VALUE",
    "CM": "explicit_witness",
    "CR": "clean_decidable",
    "HM": "journal_clean",
    "real_closure_candidate": True,
    "rationale": "test",
}))
try:
    sas.check_closure_axis(bad_path, rubric_points=False)
    check("bad enum rejects", False, "no error raised")
except sas.ClosureAxisError as e:
    check("bad enum rejects", "invalid value" in str(e))
finally:
    bad_path.unlink(missing_ok=True)
    bad_companion.unlink(missing_ok=True)

# 6) missing required field → REJECTS
miss_path = HERE / "missing_field.txt"
miss_path.write_text("OPEN GAP: missing field test\n\ntheorem foo : True := by sorry\n")
miss_companion = miss_path.with_suffix(".closure.json")
miss_companion.write_text(json.dumps({
    "CS": "full_closure",
    "CM": "explicit_witness",
    "CR": "clean_decidable",
    "HM": "journal_clean",
    # missing real_closure_candidate and rationale
}))
try:
    sas.check_closure_axis(miss_path, rubric_points=False)
    check("missing field rejects", False, "no error raised")
except sas.ClosureAxisError as e:
    check("missing field rejects", "missing required field" in str(e))
finally:
    miss_path.unlink(missing_ok=True)
    miss_companion.unlink(missing_ok=True)

if failures:
    print(f"\n{len(failures)} failure(s): {failures}")
    sys.exit(1)
print("\nAll closure-gate tests passed.")
