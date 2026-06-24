# Closure-Axis Gate — Test Documentation

**Authority**: Verifies `check_closure_axis()` in `scripts/safe_aristotle_submit.py` against the spec in `docs/closure_axis_companion_spec.md` and the taxonomy in `docs/closure_taxonomy_may30.md`.
**Test driver**: `tests/closure_gate/run_gate_test.py` (no Aristotle API calls).
**Date**: 2026-05-30. Owner: closure-execution team, Agent #2 of 5.

---

## Test fixtures

| Sketch | Companion `.closure.json` | `real_closure_candidate` | Purpose |
|---|---|---|---|
| `tests/closure_gate/sample_real.txt` | yes | `true` | Verify the happy path: real closure candidate passes the gate without any flag. |
| `tests/closure_gate/sample_bounded.txt` | yes | `false` | Verify the load-bearing case: a bounded-version submission is rejected by default and accepted with `--rubric-points`. |
| `tests/closure_gate/sample_missing.txt` | NO  | n/a   | Verify the transition-period behavior: missing companion warns and allows submission so legacy sketches do not break the flow. |

The two synthetic fixtures `bad_enum` and `missing_field` are created and torn down inside the test driver itself.

---

## Cases exercised

| # | Sketch | `rubric_points` | Expected | Observed |
|---|---|---|---|---|
| 1 | `sample_real.txt` (`real_closure_candidate=true`) | `False` | PASS, `override=False` | PASS |
| 2 | `sample_bounded.txt` (`real_closure_candidate=false`) | `False` | `ClosureAxisError` with `"real_closure_candidate=false"` and `"--rubric-points"` in the message | rejected as expected |
| 3 | `sample_bounded.txt` (`real_closure_candidate=false`) | `True` | PASS, `override=True`, log entry `RUBRIC_POINTS_OVERRIDE` | accepted as expected |
| 4 | `sample_missing.txt` (no companion) | `False` | PASS with `present=False`, WARN printed, log entry `MISSING_CLOSURE_AXIS` | warn+allow as expected |
| 5 | synthetic `bad_enum.closure.json` (`CS="NOT_A_VALID_VALUE"`) | `False` | `ClosureAxisError` with `"invalid value"` in the message | rejected as expected |
| 6 | synthetic `missing_field.closure.json` (no `real_closure_candidate`, no `rationale`) | `False` | `ClosureAxisError` with `"missing required field"` in the message | rejected as expected |

All six pass.

---

## How to run

```bash
cd /Users/patrickkavanagh/math
python3 tests/closure_gate/run_gate_test.py
```

The driver writes synthetic test files into `tests/closure_gate/` and removes them on exit. It does **not** call the Aristotle API or write to `submissions/tracking.db` (it imports `safe_aristotle_submit.py` and exercises `check_closure_axis()` in isolation).

Expected exit code: 0. Expected output ends with `All closure-gate tests passed.`

---

## What is NOT tested here

- The full `safe_submit()` async path (would require Aristotle API or a mock).
- The DB write path (`_record_closure_axis`) — that is exercised the first time a real submission happens with a companion file present; the test driver does not write to `tracking.db` to avoid polluting the schema with synthetic rows.
- The `--force` bypass — exercised structurally by the existing gap-targeting bypass and inherits its behavior.

Future work: add a pytest integration test that uses an in-memory sqlite3 DB to exercise `_record_closure_axis` upsert semantics.

---

## Failure-mode coverage matrix

The six tests above cover every branch of the gate's decision table in `docs/closure_axis_companion_spec.md` exactly once. If a future change adds a new branch (e.g., a `closure_risk_secondary` array in v1.1), append the test case here and to `run_gate_test.py`.
