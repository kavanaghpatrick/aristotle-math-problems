# U5 — Regression Tests + Historical Backfill Audit for Auto-Routing

**Author:** U5 (May 30 2026 wave, agent 5 of 5)
**Status:** Pre-U1 baseline captured, U1 verified, 12 cross-cutting integration tests added, historical audit landed, doc shipped.
**Files touched:**
- `tests/__init__.py` (already present)
- `tests/fusion_gate/__init__.py` (new — fixes pytest test-module name collision)
- `tests/closure_gate/__init__.py` (new — same fix)
- `tests/test_lane_routing_integration.py` (new — 12 tests, all passing)
- `analysis/historical_routing_audit.py` (new — backfill script)
- `analysis/historical_routing_audit.csv` (new — 1178-row audit)
- `docs/infrastructure_changes_may30/U5_regression_tests.md` (this file)

---

## 1. Baseline

| Phase | Pytest collected | Pytest passing | Standalone gate tests |
|-------|------------------|----------------|------------------------|
| **Pre-U1 (130 collected before fix)** | initially blocked by import collision between `tests/fusion_gate/run_gate_test.py` and `tests/closure_gate/run_gate_test.py` (same basename). Fixed by adding `__init__.py` to both directories so pytest scopes them as distinct packages. After fix: **130 passed**. | **130/130 PASS** | 5/5 fusion gate, all closure cases pass |
| **Post-U1 + U5 tests added** | 150 | **150/150 PASS** | 5/5 fusion gate, all closure cases pass |

Pre-U1 baseline was **130 tests**, not 98 — the task brief understated. The
delta between 130 and 150 is 20 tests:

- **8 tests** authored by U1 in `tests/test_auto_routing.py` (the 4 required
  cases + 4 regression cases U1 documented).
- **12 tests** authored by U5 in `tests/test_lane_routing_integration.py`
  (cross-cutting integration suite, see §2 below).

---

## 2. New cross-cutting tests (U5)

File: `tests/test_lane_routing_integration.py`

### 2.1 `TestDecideLane` — direct unit tests of `decide_lane()` (9 tests)

| # | Test | Coverage |
|---|------|----------|
| 1 | `test_fusion_companion_alone_auto_routes_to_fusion` | sketch + sibling `.fusion.json` → `lane=fusion`, `auto_detected=True` |
| 2 | `test_fusion_wins_over_closure_when_both_present` | both companions present → FUSION takes precedence; `closure_recommend=False` |
| 3 | `test_no_companions_routes_to_bare` | no companion → BARE (historical default), `auto_detected=False` |
| 4 | `test_bare_only_override_logs_when_fusion_companion_present` | `--bare-only` + `.fusion.json` → BARE + `BARE_OVERRIDE` audit log entry |
| 5 | `test_explicit_fusion_lane_without_companion_returns_fusion` | `--fusion-lane` flag set + no companion → `lane=fusion` from `decide_lane`, BUT downstream `check_fusion_companion()` still rejects with `FusionCompanionError` (graceful) |
| 6 | `test_explicit_informal_mode_beats_auto_detection` | `--informal-mode` + `.fusion.json` → INFORMAL (legacy explicit wins over auto-detect) |
| 7 | `test_closure_only_with_structural_reduction_recommends_fusion` | `.closure.json` with `CM=structural_finite_reduction` → BARE + `closure_recommend=True` |
| 8 | `test_closure_only_with_other_cm_no_recommendation` | `.closure.json` with `CM=journal_clean` → BARE, no recommendation |
| 9 | `test_bare_only_with_no_companion_no_override_logged` | `--bare-only` with no companion → BARE, **no** `BARE_OVERRIDE` log (regression guard) |

### 2.2 `TestAutoRoutingSmoke` — end-to-end pipeline smoke (1 test)

| # | Test | Coverage |
|---|------|----------|
| 10 | `test_end_to_end_auto_route_with_fusion_companion` | Full `safe_submit()` invocation with `Project.create` mocked. Verifies: lane banner printed, prompt rewritten by I9 informal adapter (longer than raw `.txt`), `lane='informal'` recorded in DB, `informal_mode_used=True`, `fusion_json` payload persisted. |

### 2.3 Companion-path helper conventions (2 tests)

| # | Test | Coverage |
|---|------|----------|
| 11 | `test_companion_fusion_path_convention` | `<stem>.txt` → `<stem>.fusion.json` (sibling) |
| 12 | `test_companion_closure_path_convention` | `<stem>.txt` → `<stem>.closure.json` (sibling) |

All 12 tests pass. **Total post-U1: 150/150 PASS** (130 pre-existing + 8 U1 + 12 U5).

### 2.4 I8 fusion gate fixtures (regression-verified, unchanged)

Standalone driver `tests/fusion_gate/run_gate_test.py` exercises the
`check_fusion_companion()` + `airlock_check.run_airlock()` pair:

```
PASS  1. valid bare + valid companion passes
PASS  2. leaking .txt rejected by airlock
PASS  3. oversized companion rejected by line-budget
PASS  4. missing companion rejected
PASS  5. airlock standalone detects leak
All fusion-gate tests passed (5/5).
```

The closure-axis gate (`tests/closure_gate/run_gate_test.py`) continues
to pass unchanged. U1's auto-routing did NOT touch the gate logic — both
gates run downstream of `decide_lane()` and are isolated from it.

---

## 3. Historical backfill audit

Script: `analysis/historical_routing_audit.py`
Output: `analysis/historical_routing_audit.csv` (1178 rows + header)

### 3.1 Methodology

For every row in `submissions/tracking.db`:
- Extract `filename`, `lane`, `uuid`, `problem_id`.
- Search `submissions/sketches/`, `submissions/nu4_final/`, and
  `submissions/` for a sibling `<stem>.fusion.json` (mirrors
  `_companion_fusion_path()`).
- Also try stripping `slotNNN_` prefix as a fallback.
- If companion found → `would_be_lane_now=FUSION`.
- Otherwise → `would_be_lane_now=BARE`.

### 3.2 Results

| Metric | Count |
|--------|-------|
| Total submissions audited | **1178** |
| Would be FUSION under U1 auto-routing | **5** |
| Would be BARE | 1173 |
| Routing would have changed | **0** |

The 5 FUSION-eligible submissions:

| Filename | UUID | Original lane | Companion |
|----------|------|---------------|-----------|
| erdos938_fusion | e561c214… | informal | `submissions/sketches/erdos938_fusion.fusion.json` |
| erdos267_fusion | 4f5fd762… | informal | `submissions/sketches/erdos267_fusion.fusion.json` |
| erdos1003_fusion | 4697679f… | fusion | `submissions/sketches/erdos1003_fusion.fusion.json` |
| erdos1052_fusion | a9e232a2… | informal | `submissions/sketches/erdos1052_fusion.fusion.json` |
| FT_p3_q1583_alternate_v2 | 940d518b… | informal | `submissions/sketches/FT_p3_q1583_alternate_v2.fusion.json` |

### 3.3 Headline

**Zero historical submissions would have been re-routed by U1.** Every
existing `.fusion.json` companion on disk corresponds to a submission
that was *already* manually flagged as `lane=fusion` or `lane=informal`
under the I8 (May 30 2026) opt-in workflow. The infrastructure for
authoring companions only landed earlier on the same day; nothing in
the 1173 pre-companion-era submissions had a strategy dossier to
auto-detect against.

**Interpretation:** U1's auto-routing is purely *forward-looking*. It
costs nothing on history (no behavioural change), and removes the
"forgot to pass `--fusion-lane`" footgun for everything from slot 752
onward.

---

## 4. Regression risk caught

**Risk:** the I9 informal-mode routing inside `safe_submit()` loads the
`aristotle_informal.py` adapter at runtime via
`importlib.util.spec_from_file_location(..., MATH_DIR / "scripts" / "aristotle_informal.py")`.
If a future refactor moves the adapter (or if `MATH_DIR` is shadowed in
a sub-process), the adapter silently fails to load and the submission
falls back to BARE — **without** any visible error message. The
`try / except` block at lines 1925-1934 of `safe_aristotle_submit.py`
prints a warning on exception, but a `spec is None` path is silent.

**Coverage:** `test_end_to_end_auto_route_with_fusion_companion` asserts
that the prompt actually grew (`len(prompt) > len(bare_sketch)`) AND
that `lane=informal` was recorded. If the adapter ever silently fails
to load, BOTH assertions fail loudly. This catches the regression
without needing to instrument the silent path.

A defensive follow-up would be to add an explicit warning when
`spec is None` (one-line change in `safe_aristotle_submit.py:1896`).
Out of scope for U5; flagged here for U1 or a future maintainer.

---

## 5. Auxiliary infrastructure fix

Pytest's auto-discovery was previously broken: `tests/fusion_gate/run_gate_test.py`
and `tests/closure_gate/run_gate_test.py` share a basename
(`run_gate_test`), and pytest's `rootdir`-based import strategy treated
them as the *same* module. Collection aborted with:

```
ERROR collecting tests/fusion_gate/run_gate_test.py
import file mismatch: imported module 'run_gate_test' has this __file__ attribute:
  /Users/patrickkavanagh/math/tests/closure_gate/run_gate_test.py
which is not the same as the test file we want to collect:
  /Users/patrickkavanagh/math/tests/fusion_gate/run_gate_test.py
```

**Fix:** added empty `tests/fusion_gate/__init__.py` and
`tests/closure_gate/__init__.py` so pytest scopes each as a package.
Both `run_gate_test.py` files are now collected independently. Note:
they're not authored as pytest test functions (they're standalone
drivers with `sys.exit(1)` on failure), so they get *collected* but the
pytest run is dominated by the proper `test_*.py` files. The `pytest
--collect-only` count rose from 137→… (the `run_gate_test.py` modules
collect as "modules with 0 functions" — they pass silently in the count
but their assertions run via `python3 tests/fusion_gate/run_gate_test.py`).

---

## 6. Test execution commands

```bash
# Full pytest suite (150 tests, ~2s)
python3 -m pytest tests/ -v

# Just the U5 integration tests
python3 -m pytest tests/test_lane_routing_integration.py -v

# Just U1's tests
python3 -m pytest tests/test_auto_routing.py -v

# Standalone fusion-gate driver
python3 tests/fusion_gate/run_gate_test.py

# Standalone closure-gate driver
python3 tests/closure_gate/run_gate_test.py

# Historical backfill audit
python3 analysis/historical_routing_audit.py
```

---

## 7. Summary

- **Baseline:** 130/130 PASS (was reported as 98; brief understated).
- **Post-U1 + U5:** 150/150 PASS.
- **Cross-cutting tests added:** 12 (U5) on top of U1's 8.
- **Historical audit:** 1178 submissions classified; 0 routing changes
  (5 companions on disk; all 5 were already manually tagged informal/fusion).
- **Regression risk:** silent adapter-load failure in I9 wiring; covered
  by the smoke test's two-pronged assertion (prompt length + DB lane).
- **No production code modified** outside the small `__init__.py`
  additions required to unblock pytest collection.
