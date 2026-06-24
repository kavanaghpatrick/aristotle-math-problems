# Tuza nu=4: DROP Recommendation for June 1-7 Rotation

**Date:** 2026-05-30
**Author:** Agent #9 (Tuza Feasibility Filter)
**Decision:** **DROP from active rotation.**
**Confidence (abandonment justified):** 9/10

---

## 1. Executive Summary

Apply the May 30 debate's Feasibility Filter (Codex round 2) to Tuza nu=4:

- NOT `finite-verification` — G is unbounded; claim is universal over all G with nu(G)=4.
- NOT `constructive-search` — a witness cannot prove the universal claim; the only `constructive-search` framing is a counterexample to Tuza, which Baron-Kahn ruled out as a small-scale possibility (the constant 2 cannot be improved, but the conjecture itself is widely believed).
- NOT `known-formalization` — the conjecture is genuinely open in general.
- **IS `structural-open`** — the exact class Codex flagged as ineligible for submission "until a computable subclaim exists."

After enumerating every plausible carcass candidate I could not find a computable subclaim that (a) sits outside the falsified families, (b) is not already covered by published literature, and (c) does not collapse to the same recurring bridge-coverage wall that has stopped every near-miss to date.

---

## 2. Evidence Base

### 2.1 Submission Stats (sqlite `submissions` table, `problem_id='tuza_nu4'`)

| Status            | Count |
|-------------------|-------|
| compiled_no_advance | 216 |
| compiled_partial    | 70  |
| compile_failed      | 25  |
| disproven           | 4   |
| submitted (pending) | 2   |
| **TOTAL**           | **317** |
| **compiled_advance**| **0**   |

317 submissions, zero advances, four disproofs. The disproofs include slot530 (6-packing fixed) and slot527 (two_edges_Fin12), both confirming MEMORY.md's falsified families.

### 2.2 Falsified Approach Families (per `mk failed tuza` and `failed_approaches` table)

1. **Apex-based bridge coverage** — apex assumed away from B; counterexample.
2. **6-packing** — disproven on Fin12 attempt.
3. **LP duality / universal apex** — never produced a closing argument.
4. **bridges_inter_card_eq_one** — two bridges can share more than v; disproven.
5. **bridge_outer_vertex_unique** — an outer vertex can appear in multiple bridges; disproven.
6. **bridge_hit_by_Se_cover** — S_e covers do NOT absorb bridges automatically.
7. **external_shares_unique_element** — externals can bridge multiple M-elements.
8. **cycle_opposite_disjoint** / **path_nonadjacent_disjoint** — sharing-graph structure does not imply vertex-disjointness.

### 2.3 Recurring Sorry Pattern (last 5 near-misses)

| Slot   | Where sorry sits | Pattern |
|--------|------------------|---------|
| 327    | `tau_le_8` final assembly + `two_edges_cover_X_and_externals` | bridge coverage by 2-edge selection |
| 324    | `tau_le_8` direct | bridge coverage |
| 331    | `tau_le_8` direct (with full sketch) | bridge coverage by apex selection |
| 269    | `path4_cover_covers` | bridge t in path4 cover |
| 532    | `bridge_covered_by_apex_selection` + 5-packing extraction | bridge coverage |

**The single most recurring sorry — gold for any future Tuza work — is:**

> *Every "bridge" triangle B (a triangle that shares one edge each with two distinct M-elements X, Y) is hit by the 2-edges-per-M-element selection.*

Every working sketch reduces the entire problem to this lemma. The lemma is FALSE under the apex-based selection (slot 26 counterexample: bridges t1={0,1,3}, t2={0,1,4} share {0,1}, so apex-based edges can miss both). The lemma is TRUE only if one specifies a non-apex selection rule, and every non-apex rule attempted to date has either been disproven or just relocates the sorry.

### 2.4 Literature Coverage (rules out small/structural carcasses)

- **Treewidth <= 6**: Tuza proven (Botler et al.). For nu=4 the relevant G has nontrivial treewidth, but any small-treewidth-restricted subclaim is already published — not novel.
- **Max average degree < 7**: Puleo proven.
- **K_4-free**: Krivelevich proven.
- **Planar / chordal / threshold / K_{3,3}-subdivision-free**: all proven.
- **Random graphs G(n,m)**: Kahn-Park (2024-ish) proven for all m.
- **Tight only for K_4, K_5**: known. So the only nu=4-specific extremal cases are well-understood.

There is no narrow graph class for which a Tuza nu=4 subclaim is BOTH open AND computable.

### 2.5 Counterexample Search Angle (the only `constructive-search` framing)

Submitting "find G with nu(G)=4 and tau(G) > 8" is mechanically `constructive-search`, but:

- The conjecture is widely believed.
- Baron-Kahn made the constant 2 tight but never produced a finite counterexample to the basic Tuza inequality.
- 317 prior submissions implicitly searched the small-case space and found nothing.
- Aristotle is not a SAT solver; counterexample search at scale is not its strength.

Confidence that a sub-100-vertex counterexample exists: < 5%.

---

## 3. Reasoning for DROP (not Carcass)

A viable carcass must satisfy three tests:

1. **Outside falsified families** — yes for some bounded-degree framings, but...
2. **Not in literature** — fails. Bounded-degree, max-avg-degree, low-treewidth, K_4-free are all published.
3. **Not the same recurring bridge wall** — fails. Every reformulation I can articulate (`tau_le_8 for G with maxSharingDegree(M) <= 2`, `bridge-coverage on Fin n for n <= 9`, etc.) either has been attempted (slot40 `tau_bridges_sparse_sharing` compiled clean but never closed the global goal) or reduces to the same wall.

The honest assessment: the bridge wall is a real combinatorial obstruction. Tuza nu=4 as a Lean target is gated by an unsolved combinatorial step that humans have not closed either — that is exactly what `structural-open` means.

---

## 4. Recommendation

1. **Remove `tuza_nu4` from active rotation for the June 1-7 batch.**
2. **Re-label `tuza_nu4` as `structural-open` in any feasibility-filter index.**
3. **Do not re-submit until a new structural diagnostic appears.** Three concrete triggers that would justify reactivation:
   - A new published result (post-2025) that gives a fresh computable subclaim.
   - A successful breakthrough on bridge coverage in a separate problem (e.g. nu=3 with a non-apex selection rule that lifts).
   - A confirmed sub-100-vertex graph G with nu(G)=4 and tau(G) > 8 (which would falsify Tuza and reframe the problem entirely).
4. **Preserve the 67 cleanly-compiled scaffolding lemmas in `submissions/nu4_final/`.** They are real mathematics and will plug into any future attempt.
5. **Archive the recurring bridge-coverage wall as the single most valuable knowledge transfer.** Future agents should know: any sketch that reduces Tuza nu=4 to "bridges hit by the selection" is doomed under apex-based selection, and no non-apex selection has yet survived audit.

---

## 5. Should Tuza nu=4 Ever Return to Active Rotation?

**Honest assessment:** Not within the current Aristotle paradigm. The problem is `structural-open` in the strongest sense — every Lean-amenable reduction we have produced hits the same combinatorial wall that has stopped human mathematicians for 45 years. Aristotle excels at `finite-verification` and `constructive-search`; it has produced 317 submissions on Tuza nu=4 without ever crossing the bridge-coverage gap. Continuing to submit is metric-chasing.

It should return only if (a) external mathematical progress provides a new tool, or (b) the pipeline gains a genuinely new capability (e.g. structured search over combinatorial selection rules guided by SAT solvers). Until then it is a memorial in the failed_approaches table, not an active target.
