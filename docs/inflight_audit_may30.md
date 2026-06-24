# Inflight + Recent Submissions Audit (S4 — May 30 2026)

**Agent:** S4 (audit of 10)
**Scope:** Inflight slot 746 + recent batch (slot 741-745) + historical backfill for slot 736-740.
**Tools applied retroactively:** closure-axis companions (X2), `mathematical_content_score` (I2), `literature_check.py` (I4), revised `gather_context()` (I1).

---

## 1. Inflight / recent batch status

All six referenced jobs returned status `COMPLETE` (or `COMPLETE_WITH_ERRORS`,
which is downloadable — see `aristotle_fetch.py`).  Result files have not
yet been fetched.

| Slot | UUID | Project | Aristotle status | DB row |
|---|---|---|---|---|
| 741 | `7031f637-54ed-4362-9456-5b4e27e038e0` | erdos647_cunningham_residual_35 | COMPLETE | not yet tracked |
| 742 | `bdc60eff-04a7-4c15-b469-bcd118b443c6` | erdos203_sierpinski_1d_benchmark | COMPLETE_WITH_ERRORS | not yet tracked |
| 743 | `8d9e29b3-c099-4fea-beb2-aab7ed76fb99` | erdos203_grid_12x12_B1000 | COMPLETE | not yet tracked |
| 744 | `22dafcc6-0afa-4769-b293-c368b97ade0b` | FT_p3_q1583_alternate | COMPLETE_WITH_ERRORS | not yet tracked |
| 745 | `8e353fc6-c165-4df2-9577-088dea34eb52` | brocard_nrange_1001_2000 | COMPLETE | not yet tracked |
| 746 | `65da8d8c-4059-4454-b3b4-ea2e3b87ede7` | odd_multiperfect_sigma0_11 | COMPLETE_WITH_ERRORS | row id 1258 |

Recommendation: **fetch + audit all six now** — `COMPLETE_WITH_ERRORS` is the
expected status for a closure-axis submission that compiled but didn't
fully resolve the conjecture; the Lean artifact is still downloadable and
needs to be processed for `target_resolved` evaluation.

(Caller note: `aristotle_fetch.py status` crashed during the audit on a
gzipped legacy result file (`UnicodeDecodeError` at slot 685's
`ebabb371-f2f...` Casas-Alvero artifact).  The status command was
re-implemented inline; the legacy file should be either decoded as gzip
or ignored — separate fix.)

---

## 2. Retroactive closure-axis assignments (slot 741-746)

Six `.closure.json` companions were authored on May 30 — one for each
slot.  All live in `submissions/sketches/` alongside the parent `.txt`.

| Slot | CS | CM | real_closure | Hedge? |
|---|---|---|---|---|
| 741 | `sub_claim_closure` | `witness_table_chunked` | true | no — clean sub-claim |
| 742 | `formalization_only` | `witness_table_chunked` | false | calibration benchmark |
| 743 | `bounded_version_closure` | `witness_table_chunked` | false | yes (likely unsat) |
| 744 | `sub_claim_closure` | `structural_finite_reduction` | true | single-q family boundary |
| 745 | `bounded_version_closure` | `witness_table_chunked` | false | range bump only |
| 746 | `sub_claim_closure` | `structural_finite_reduction` | true | clean p-adic argument |

Files:
- `/Users/patrickkavanagh/math/submissions/sketches/erdos647_cunningham_residual_35.closure.json`
- `/Users/patrickkavanagh/math/submissions/sketches/erdos203_sierpinski_1d_benchmark.closure.json`
- `/Users/patrickkavanagh/math/submissions/sketches/erdos203_grid_12x12_B1000.closure.json`
- `/Users/patrickkavanagh/math/submissions/sketches/FT_p3_q1583_alternate.closure.json`
- `/Users/patrickkavanagh/math/submissions/sketches/brocard_nrange_1001_2000.closure.json`
- `/Users/patrickkavanagh/math/submissions/sketches/odd_multiperfect_sigma0_11.closure.json` (pre-existing)

Three real-closure candidates (741, 744, 746) qualify for `lane='closure'`
under the I2 lane resolution precedence.

---

## 3. `mathematical_content_score` backfill

Per the user directive, S4 records F1-axis scores for slot 736-740 and
extends scoring to the May 30 batch (slot 741-746).

### Sidecar table

The I2 migration assumed slot 736-739 would be in DB by `slot{N}_%`
filename prefix; they aren't (these were direct-CLI submissions before DB
tracking became routine).  S4 introduces a sidecar table
`mcs_pending_backfill` (created idempotently) that queues verdicts until
the actual DB row lands.  On every run, `apply_pending()` joins the queue
back to `submissions` by uuid → filename → slot-prefix, applies the score,
and marks `applied_at`.

### Verdicts queued (11 total)

| Slot | Score | Lane | Note |
|---|---:|---|---|
| 736 | 1 | bare | PURE COMPUTE (F1 verdict) |
| 737 | 8 | bare | STRUCTURAL — real σ₀ multiplicativity |
| 738 | 3 | bare | COMPUTE + GLUE |
| 739 | 7 | bare | real algebra |
| 740 | 2 | bare | Python external + native_decide; structural plan, compute proof |
| 741 | 6 | closure | Sub-claim closure; 35-row witness cascade |
| 742 | 1 | bare | Calibration / formalization-only benchmark |
| 743 | 2 | bare | Bounded extension of slot740; honest hedge |
| 744 | 5 | closure | Sub-claim closure; FT q=1583 family-boundary prime |
| 745 | 2 | bare | Range-bump bounded version |
| 746 | 4 | closure | Sub-claim closure via slot737 multiplicativity DNA |

### Application status

| Slot | Status | Notes |
|---|---|---|
| 736-740 | queued | rows not in DB; will apply when a future `/fetch` or `/track` adds them |
| 741-745 | queued | submitted via direct project id, never tracked |
| 746 | **APPLIED** | DB row 1258 now has `mathematical_content_score=4`, `lane='closure'` |

Backfill script: `/Users/patrickkavanagh/math/scripts/backfill_mcs_may30_s4.py`
- Idempotent (re-runs are no-ops once `applied_at` is set)
- Creates `mcs_pending_backfill` if missing
- Two operations: `queue_verdicts()` and `apply_pending()`

---

## 4. Literature-check sweep

Ran `scripts/literature_check.py --skip-arxiv --json` against each sketch.

| Slot | problem_id | status | wiki | erdosproblems | Verdict |
|---|---|---|---|---|---|
| 741 | erdos_647_cunningham_chain_residual | UNKNOWN | CLEAR | n/a | safe to submit |
| 742 | erdos_203_1d_sierpinski_analog | CLEAR | CLEAR | open | safe to submit |
| 743 | erdos_203_12_12 | UNKNOWN | CLEAR | n/a | safe to submit |
| 744 | feit_thompson_p_3_q_1583 | UNKNOWN | CLEAR | n/a | safe to submit |
| 745 | brocard_1001_2000 | UNKNOWN | CLEAR | n/a | safe to submit |
| 746 | odd_multiperfect_sigma0_11 | UNKNOWN | CLEAR | n/a | safe to submit |

Cross-checked against `analysis/literature_kill_list.csv`: none of the six
problem ids appear there.  No `AI_CLOSED` or `RECENTLY_SOLVED` hits.

Background hits worth noting for the underlying parent problems:
- `erdos_647`: AMBIGUOUS (partial AI progress) — slot 741 is a strict
  delta on prior AI work, ack requirement met by slot737 precedence in
  the sketch.
- `erdos_124`: AMBIGUOUS (recorded `LITERATURE_ACK_RECORDED` on
  2026-05-30) — not in this batch.

---

## 5. What-if context analysis (post-I1 fix)

The pre-May-30 `gather_context()` returned 0 rows for every submission
because the status-enum filter intersected the empty set with the new
schema. The I1 fix replaces the filter with `output_file IS NOT NULL` +
`status != 'compile_failed'`.

Per-slot impact, if the new `gather_context()` had been live at submission time:

| Slot | Prior artifacts found (post-fix) | Impact on submission |
|---|---:|---|
| 741 (erdos_647) | 0 attached (2 in DB but missing on disk in Downloads) | unchanged — old artifacts already gone |
| 742 (erdos_203) | 1 (`slot724_erdos203_result.lean`) | **MARGINAL** — adds 1 file; calibration not affected |
| 743 (erdos_203) | 1 (`slot724_erdos203_result.lean`) | **MODERATE** — same artifact; the 12x12 grid attempt would have inherited the slot724 covering-system context |
| 744 (feit_thompson) | **9 artifacts** (slot720_iter2, slot613, slot612, slot611, slot610, ...) | **HIGHEST IMPACT** — the q=1583 diagnostic explicitly references slot720's `not_dvd_via_fermat_factor` helper; auto-attaching `slot720_iter2_ft_family_result.lean` plus the slot610-613 family of p=3 lemmas would have given Aristotle the exact Lean machinery it needed. |
| 745 (brocard) | 2 (`slot722_iter2_brocard_extended_result.lean`, `slot605_brocard_result.lean`) | **HIGH** — slot722's chunked native_decide IS the technique slot745 is range-bumping; auto-attaching it would have saved a re-derivation. |
| 746 (multiperfect) | 0 (canary warning fires: 1 prior submission but 0 artifacts) | unchanged — multiperfect is a new problem_id |

**Single biggest miss:** **slot 744 (FT q=1583)**.  Nine prior FT
artifacts (slot610-613 + slot720 family closure) would have auto-attached,
giving Aristotle the exact helper lemmas the sketch explicitly invokes.
The slot was submitted on 2026-05-30 13:36 without these.

**Second biggest:** **slot 745 (Brocard [1001,2000])**.  Slot722 is the
direct technical predecessor and its compiled result file was sitting in
the DB but not being attached.

---

## 6. Re-submission recommendation

Given the impact analysis, the candidates for re-submission under the
new pipeline (with I1 gather_context() live, closure-axis companions
attached, and literature check passed) are:

| Slot | Re-submit? | Justification |
|---|---|---|
| 741 | **wait** | Prior artifacts missing on disk; nothing to attach.  Fetch the existing result first. |
| 742 | no | Calibration benchmark; new context wouldn't materially change a 1-D Sierpinski formalization. |
| 743 | **maybe** | If the existing result is COMPLETE_WITH_ERRORS for compute reasons (witness explosion), a resub with slot724_erdos203_result.lean attached might tip it. |
| 744 | **YES — highest priority** | Nine prior artifacts should have been attached; this is the textbook case of the pre-I1 silent failure. |
| 745 | **YES — second priority** | slot722 result file IS the technique being range-bumped.  Auto-attaching it should be substantially better. |
| 746 | no | No prior multiperfect artifacts exist; the canary warning is correct.  Wait for the inflight result. |

**Action gate:** Do NOT re-submit until S5+ have audited the COMPLETED
result files for each slot.  A re-submission that ignores
`compiled_advance` for a slot is wasted compute.

---

## 7. Artifacts and references

- Closure JSON companions: `submissions/sketches/*.closure.json`
- Backfill script: `scripts/backfill_mcs_may30_s4.py`
- Sidecar table: `submissions.mcs_pending_backfill`
- DB row updated: `submissions.id=1258` (slot 746, multiperfect)
- Literature kill list (consulted, no hits): `analysis/literature_kill_list.csv`
- Related infrastructure docs: `docs/infrastructure_changes_may30/I1`,
  `I2`, `I3`, `I4`

End S4 audit.
