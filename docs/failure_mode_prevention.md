# Failure-Mode Prevention Checklist (S7, 2026-05-30)

**Authority**: Operationalizes the F1-F10 failure catalog from `analysis/failure_dna_may30.md`.
**Owner**: S7 of 10 — failure-mode prevention agent.
**Status**: ACTIVE 2026-05-30.

---

## Why

Agent F3's audit of 25 `compiled_no_advance` results identified 10 recurring failure modes that produce clean-compiling Lean files but do NOT resolve the open gap. F1 alone accounts for 44% of the no-advance bucket. Some failure modes were already caught by existing gates (F2 em-tautology, F8 vacuous iff via the closure-axis CR enum). The rest were not.

This document maps each failure mode to:
1. The pre-submission check that catches it (if any).
2. The post-audit check that catches it (if any).
3. The existing gate or skill that already handled it.
4. The schema constraint that prevents it.

It is the single source of truth for "which F-modes are we systematically preventing, and where in the pipeline."

---

## Master mapping

| F-code | Mode | Pre-submission check | Post-audit check | Existing gate/skill | Schema constraint |
|---|---|---|---|---|---|
| F1 | Iff.rfl trap (undecidable wrapper) | `_check_f_modes_pre_submission` F1 rule in `check_gap_targeting`: detects `Irrational/Tendsto/IsEquivalent/HasDensity/Set.Infinite/Filter.atTop/Cardinal.aleph` AND no `Finset.range/Icc`. HARD REJECT when no rescue, WARN otherwise. | `_detect_f1_iff_rfl` in `audit_proven.py`: detects `theorem ... ↔ ... := Iff.rfl` or `:= by rfl` (CRITICAL). | None (was missed by every gate before S7). | Closure-axis: `CR=iff_rfl_trap` AND `real_closure_candidate=true` → REJECT (F1-coherence). |
| F2 | EM tautology (P ∨ ¬P) | `_looks_like_em_tautology` in `check_gap_targeting` C6 — HARD REJECT. | `audit_file` em-tautology block — CRITICAL downgrade. | C6 gate (added 2026-05-28 from PILOT_ERDOS850). | Closure-axis: `CR=em_tautology` AND `real_closure_candidate=true` → REJECT (F2-coherence). |
| F3 | Side-lemma proliferation without main target | `_check_f_modes_pre_submission` F3 rule: detects hand-wave phrases `reduces to`, `follows from classical/standard`, `infinite descent`, `sieve method`, `Pell theory`. WARN. | `_detect_f3_side_lemmas` in `audit_proven.py`: ≥15 proven decls AND no decl name matches problem_id → HIGH. | None before S7. | Closure-axis: `CR=infrastructure_overgrowth` AND `real_closure_candidate=true` → REJECT (F3-coherence). |
| F4 | Axiomatize-the-hard (exact?/apply?/rewrite? stubs) | `_check_f_modes_pre_submission` F4 rule: detects `by classical`, `by standard`, `well-known/classical/standard result/fact/theorem`. WARN. | `_detect_f4_exact_query` in `audit_proven.py`: counts `exact?`/`apply?`/`rewrite?` in code (HIGH). | None before S7. | None — F4 is a process failure, not a classification disagreement. |
| F5 | Recursive falsification (Tuza ν=4 specifically) | Cannot detect from sketch alone — requires knowing the problem's falsified-approach record. Operator must check `mk failed <keywords>` before submitting. | Detected only by /audit on a per-submission basis; no structural detector — the witness graph compiles but the corollary contradicts the original. | `mk failed` skill + `MEMORY.md` FALSIFIED list. | Closure-axis: `CR=recursive_falsification` AND `real_closure_candidate=true` → REJECT (F5-coherence). |
| F6 | Restate-with-sorry (Tuza/path4) | Cannot reliably detect from sketch — operator must check `mk context <problem>` before submitting falsified-approach-saturated problems. | `_detect_f6_restate_with_sorry` in `audit_proven.py`: detects Aristotle's meta-failure marker + `sorry` (CRITICAL). | Existing `sorry_count > 0` rule already downgrades to `compiled_partial`. F6 detector adds the diagnostic root cause. | None — F6 is a Tuza-specific pattern, caught via `sorry_count` + closure HM. |
| F7 | Bounded verification dressed as infinite claim | Closure-axis schema: `CS=bounded_version_closure` AND `real_closure_candidate=true` → REJECT (F7-coherence rule in `_check_closure_axis_consistency`). | No structural detector needed — the bounded shape was disclosed in the closure-axis at submission time. If misclassified there, it would have been rejected before submission. | Closure-axis gate (added 2026-05-30). | YES — F7-coherence rule rejects the contradictory combination outright. |
| F8 | Vacuous equivalence (Iff.rfl on definition) | Same as F1 — same detector pattern, same classification. | Same as F1 — `_detect_f1_iff_rfl` covers both. | None before S7 (apart from CR enum). | Closure-axis: `CR=iff_rfl_trap` AND `real_closure_candidate=true` → REJECT. |
| F9 | Computational explosion (`native_decide` fan-out) | Cannot reliably detect from sketch — fan-out is data-dependent. Operator must estimate cells × ops. | `_detect_f9_bounded_dressed` in `audit_proven.py`: `theorem ...: ... ≤ <literal> ... := by` AND `native_decide` (HIGH). | Closure-axis CR=witness_search_explosion (informational). | None — F9 is recoverable via chunking (witness_table_chunked). |
| F10 | Definition mismatch with formal-conjectures | `_check_f_modes_pre_submission` F10 rule: detects `^def`, `^class`, `^structure`, `^instance`, `^abbrev` in sketch (WARN). | None — F10 is a definitional drift that requires hand inspection of upstream sources. The closure-axis `CR=definition_mismatch` is the post-audit honesty label. | None. | Closure-axis: `CR=definition_mismatch` AND `real_closure_candidate=true` → REJECT (F10-coherence). |

---

## Pre-submission gate summary

The pre-submission gate in `scripts/safe_aristotle_submit.py` now has the following ordered checks (each rejects on failure):

1. **C1-C5** (existing): file format / line count / strategy keywords / Lean code volume.
2. **C6** (existing): EM tautology — hard reject.
3. **C7** (S7, NEW): F-mode warnings via `_check_f_modes_pre_submission`. F1-no-range becomes a hard reject; F3/F4/F10 produce stdout warnings logged as `F<n>_WARNING`.
4. **Literature freshness** (existing).
5. **Closure-axis** (existing + S7 enhancement): schema validation + `_check_closure_axis_consistency` for F1/F2/F3/F5/F7/F10-coherence.
6. **Fusion-companion** (existing).
7. **Rate limit / capacity / lockfile**.

---

## Post-audit detector summary

`scripts/audit_proven.py::detect_failure_modes` runs these detectors against every audited Lean file. Each appends an `(severity, "F<n>: ...")` entry to the issues list; the existing audit machinery then downgrades the DB row accordingly.

| Detector | Function | Severity | Trigger |
|---|---|---|---|
| F1/F8 Iff.rfl | `_detect_f1_iff_rfl` | CRITICAL | `theorem ... := Iff.rfl` / `:= by rfl` shape OR `def answer` + `Iff.rfl` co-occurrence |
| F3 side-lemmas | `_detect_f3_side_lemmas` | HIGH | ≥15 proven decls AND no decl name matches the file's problem-id hint |
| F4 exact? trail | `_detect_f4_exact_query` | HIGH | ≥1 `exact?` / `apply?` / `rewrite?` in code |
| F6 restate-with-sorry | `_detect_f6_restate_with_sorry` | CRITICAL | Aristotle meta-failure marker + `sorry` |
| F9 bounded native_decide | `_detect_f9_bounded_dressed` | HIGH | `theorem ... ≤ <literal> ... := by` + `native_decide` |

F2 / F5 / F7 / F10 are intentionally not in this list:
- F2 is already detected by the dedicated em-tautology block above F-mode detection.
- F5 (recursive falsification) is too problem-specific for a static detector.
- F7 is prevented by the closure-axis schema coherence rule; no post-audit need.
- F10 (definition mismatch) requires comparing the file to its upstream formal-conjectures source — out of scope for static audit. The honest CR label is the recourse.

---

## The single most-common failure mode and how we now prevent it

**F1 / F8 (Iff.rfl trap on undecidable wrappers)** — 44% of the no-advance sample.

Prevention chain:
1. **Pre-submission HARD REJECT**: any sketch using `Irrational/Tendsto/IsEquivalent/HasDensity/Set.Finite/Set.Infinite/Filter.atTop/Cardinal.aleph` in the theorem body, without a `Finset.range/Icc/Ico/Ioc/Ioo`, `≤ N`, or `Decidable` rescue elsewhere in the sketch, is rejected outright by `check_gap_targeting` C7.
2. **Pre-submission WARN**: any other pre-submission F-mode signature (F3 hand-wave, F4 hard-defer, F10 local def) prints a warning and logs `F<n>_WARNING` for batch audit.
3. **Schema-level REJECT**: a closure-axis with `CR=iff_rfl_trap` AND `real_closure_candidate=true` cannot pass the gate — the agent's own honest classification is forced to be consistent.
4. **Post-audit CRITICAL downgrade**: if F1 slips through (e.g. operator used `--force`), `_detect_f1_iff_rfl` in `audit_proven.py` flags the file CRITICAL and downgrades to `compiled_no_advance`.

This is a 4-layer defense. Layer 1 (the hard reject) covers the vast majority; layers 2-4 are the safety net.

---

## F-mode we cannot prevent structurally (enforce via post-audit only)

**F5 (recursive falsification, Tuza ν=4 specifically).**

Why we can't prevent it pre-submission:
- F5 fires when Aristotle constructs a graph that satisfies one premise but violates another, and the resulting corollary contradicts the original lemma's antecedent. This is mathematical content, not a syntactic pattern. The sketch looks fine; the contradiction emerges from Aristotle's choice of witness graph.
- The only signal we have is "the problem has a falsified-approach record" (in `mk failed` / `MEMORY.md`), and any apex/bridge/cycle-shaped sub-claim is a candidate. But not every sub-claim on a falsified-record problem is F5 — some are simply infrastructure that compiles cleanly without making a claim that contradicts the prior falsification.

Enforcement:
- Operator MUST run `mk failed <keywords>` before submitting on `tuza_nu4`, `path4_tau_le_8`, `leinster`, `agoh_giuga`. The `feasibility_filter_rubric.md` classifies these as `structural-open` with HOLD entry condition.
- Post-audit: closure-axis `CR=recursive_falsification` AND `HM=infrastructure_only` is the honest label, and the schema coherence rule rejects any attempt to combine these with `real_closure_candidate=true`.

---

## How to add a new F-mode detector

1. Add the catalog entry to `analysis/failure_dna_may30.md`.
2. If the F-mode has a pre-submission red flag, add the regex(es) to one of the `F<n>_*` constants in `scripts/safe_aristotle_submit.py` and add a branch to `_check_f_modes_pre_submission`.
3. If the F-mode has a post-audit signature, add a `_detect_f<n>_*` function in `scripts/audit_proven.py` and register it in `detect_failure_modes`.
4. If the F-mode has a closure-axis coherence rule, add it to `_check_closure_axis_consistency` AND to the F-mode mapping table in `docs/closure_axis_companion_spec.md`.
5. Add a fixture sketch and a unit test in `tests/test_failure_mode_detection.py` that asserts the detector fires.
6. Update this document with a new row in the master mapping table.

---

## References

- `analysis/failure_dna_may30.md` — F1-F10 catalog, frequencies, examples.
- `docs/closure_taxonomy_may30.md` — closure axis enum definitions.
- `docs/closure_axis_companion_spec.md` — schema + gate behaviour.
- `scripts/safe_aristotle_submit.py` — pre-submission gate implementation.
- `scripts/audit_proven.py` — post-audit detectors.
- `tests/test_failure_mode_detection.py` — unit tests for all detectors.
- `docs/research/PILOT_ERDOS850.md` — origin of the em-tautology rule (F2 antecedent for this work).
