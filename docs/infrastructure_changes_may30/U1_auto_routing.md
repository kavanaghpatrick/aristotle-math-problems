# U1 — Auto-Routing: FUSION-by-default for Novel Structural Problems

**Author:** U1 (May 30 2026 wave, agent 1 of 5)
**Status:** Decision logic shipped, CLI wired, `mk submit` convenience added, 8 tests passing.
**Files touched:**
- `scripts/safe_aristotle_submit.py` — added `decide_lane()`, `--bare-only` flag, banner output.
- `math-forge/scripts/mk` — rewrote `mk submit` with companion pre-check + confirmation gate.
- `tests/test_auto_routing.py` — 8 tests covering the 4 required cases + 4 regression cases.
- `docs/infrastructure_changes_may30/U1_auto_routing.md` — this file.

---

## 1. Motivation

I9 (May 30 2026) confirmed empirically (smoke test on Euclid's theorem,
UUID `8d500201`) that the **prompt shape** flips Aristotle between two
subsystems:

| Subsystem | Prompt shape | Output type |
|-----------|-----------------------------------|-------------|
| #1 (MCGS) | `theorem ... := by sorry` attached as tar | Lean proof or fail |
| #2 (informal reasoner) | natural-language statement + outline | Lemma decomposition + REPL-formalized output |

**All four known Aristotle Erdős wins** (E124, E728, E1026, E481) used
subsystem #2. This project's pipeline routed 100% of submissions to
subsystem #1. That gap is the entire 0.8% hit-rate problem.

The I9 wiring made informal mode *available* via the `--fusion-lane` /
`--informal-mode` explicit flags, but it stayed opt-in. U1 makes it the
**default** for novel structural problems — any submission with a
`.fusion.json` companion now auto-routes to subsystem #2.

---

## 2. Decision logic

`decide_lane(input_file, fusion_lane_explicit, informal_mode_explicit, bare_only)`
returns the chosen lane and the flags to forward to `safe_submit()`.

| Precedence | Condition | Lane | Notes |
|------------|-----------|------|-------|
| 1 | `--bare-only` flag set | BARE | If a `.fusion.json` existed, logs `BARE_OVERRIDE`. |
| 2 | `--fusion-lane` flag set | FUSION | Legacy explicit override — preserves existing pipelines. |
| 3 | `--informal-mode` flag set | INFORMAL | Legacy explicit override. |
| 4 | `<stem>.fusion.json` present | FUSION (auto) | Engages subsystem #2 via I9 routing downstream. |
| 5 | `<stem>.closure.json` with `CM=structural_finite_reduction` | BARE | Prints recommendation; does NOT auto-promote. |
| 6 | `<stem>.closure.json` with other `CM` | BARE | Mentions companion in banner, no recommendation. |
| 7 | No companion | BARE | Historical default. |

The chosen lane is **always** printed at the top of `safe_submit()`
output:

```
🚦 Lane: FUSION (auto-detected via slot999_test.fusion.json companion). Override with --bare-only.
```

When `closure_recommend` fires, a separate hint appears:

```
   💡 Recommendation: this problem has a structural_finite_reduction classification.
      Consider authoring a .fusion.json companion (with informal_proof_outline)
      to engage Aristotle's lemma-based reasoner (subsystem #2). Closure-only
      auto-routes to BARE; the recommendation does NOT promote the lane.
```

**Important:** `--force` skips the auto-router entirely. The orchestrator
pipeline owns its own lane decision through `--force`, just as before.
This keeps `safe_aristotle_submit.py` backward-compatible with the
informal-proof bypass that the orchestrator already depends on.

---

## 3. CLI changes

### Before / after

| Behaviour | Before | After |
|-----------|--------|-------|
| Default lane (no flags, no companion) | BARE | BARE (unchanged) |
| Default lane (no flags, `.fusion.json` present) | BARE | **FUSION (auto)** |
| Default lane (no flags, `.closure.json` SFR present) | BARE | BARE + recommendation banner |
| `--fusion-lane` flag | FUSION | FUSION (unchanged, explicit) |
| `--informal-mode` flag | INFORMAL | INFORMAL (unchanged, explicit) |
| Force BARE despite a `.fusion.json` | (no clean way; had to delete companion) | **`--bare-only`** |
| Lane visibility | hidden in body of stdout | top-line banner `🚦 Lane: ...` |

### Flags table

| Flag | Type | Purpose |
|------|------|---------|
| `--fusion-lane` | explicit override | Force FUSION (legacy, kept for pipelines that already pass it). |
| `--informal-mode` | explicit override | Force INFORMAL (legacy). |
| `--bare-only` | explicit override **(new)** | Force BARE; logs `BARE_OVERRIDE` if a `.fusion.json` existed. |
| `--force` | bypass | Skips gap-targeting, closure-axis, AND auto-routing. Caller owns lane. |

---

## 4. `mk submit` convenience

`mk submit <file>` wraps `safe_aristotle_submit.py` with:

1. **Companion pre-check** — prints which companion files are present
   adjacent to the sketch.
2. **Lane banner** — declares the lane that will be used *before*
   submitting.
3. **Confirmation prompt** — requires `y` / `--yes` to proceed. In
   non-interactive sessions without `--yes`, the command aborts with
   exit code 2 (so accidental piped invocations cannot submit
   silently).
4. **`--bare-only` pass-through** — the flag is consumed locally for
   the banner AND forwarded to `safe_aristotle_submit.py`.

Example invocations:

```bash
# Interactive submission with auto-detected lane:
mk submit submissions/sketches/erdos938.txt

# Non-interactive (CI / orchestrator-style):
mk submit submissions/sketches/erdos938.txt --yes

# Force BARE even though a .fusion.json companion exists:
mk submit submissions/sketches/erdos938.txt --bare-only --yes
```

---

## 5. Backward compatibility

- The existing `--fusion-lane` explicit override flag retains its full
  semantics: tag the submission as `DB.lane='fusion'`, trigger the
  fusion-companion gate, run the airlock. The decision now happens at
  the *top* of `safe_submit()`, but the gate runs exactly where it did
  before.
- The existing `--informal-mode` flag still routes to the informal
  reasoner via the I9 wiring at lines 1672+.
- The orchestrator's `--force` bypass is unchanged: it skips the
  auto-router so the orchestrator can drive lane selection itself.
- All 5 previous fusion-gate tests still pass (`tests/fusion_gate/run_gate_test.py`).
- All 6 previous gather_context tests still pass.
- All 13 previous submit-capacity tests still pass.
- 3 previous schema-consistency tests still pass.

Total previous tests verified passing: 27.

---

## 6. Tests

`tests/test_auto_routing.py` — 8 tests, all passing:

| # | Test | Asserts |
|---|------|---------|
| 1 | `test_case1_fusion_companion_auto_routes_to_fusion` | `.fusion.json` present → `lane=fusion, auto_detected=True, fusion_lane=True`. |
| 2 | `test_case2_closure_structural_finite_reduction_recommends` | `.closure.json` with `CM=structural_finite_reduction` → `lane=bare, closure_recommend=True`. |
| 3 | `test_case3_no_companion_silent_bare` | no companion → `lane=bare, auto_detected=False, closure_recommend=False`. |
| 4 | `test_case4_bare_only_override_logs_event` | `.fusion.json` + `--bare-only` → `lane=bare, override=BARE_OVERRIDE`, log entry written. |
| 5 | `test_explicit_fusion_lane_flag_still_works_without_companion` | `--fusion-lane` without companion → `lane=fusion, auto_detected=False`. |
| 6 | `test_closure_without_structural_finite_reduction_no_recommend` | `.closure.json` with `CM=explicit_witness` → `lane=bare, closure_recommend=False`. |
| 7 | `test_fusion_takes_precedence_over_closure_when_both_present` | Both companions present → `lane=fusion, closure_recommend=False`. |
| 8 | `test_explicit_informal_mode_flag_routes_to_informal` | `--informal-mode` → `lane=informal, auto_detected=False`. |

Run:

```bash
python3 -m pytest tests/test_auto_routing.py -v
```

Output (2026-05-30):

```
============================== 8 passed in 0.06s ==============================
```

---

## 7. The single most important change in user behaviour

**Authoring a `.fusion.json` companion next to a sketch is now the
only action needed to flip a submission from MCGS-only (subsystem #1)
to the lemma-based informal reasoner (subsystem #2).** No CLI flag
required, no edits to existing pipelines required, no opt-in code path
to remember. The default does the right thing.

Previously the only way to engage subsystem #2 was to remember and
type `--fusion-lane` (or `--informal-mode`); historically nobody did,
which is why 0% of submissions used the reasoner that powered every
known Erdős win.
