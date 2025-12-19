# Tuza Work Timeline/Changelog

This changelog documents the progression of Tuza work, including version submissions, key changes, and results.

**See [TUZA_COMPLETE_HISTORY.md](TUZA_COMPLETE_HISTORY.md) for the DEFINITIVE comprehensive documentation.**

---

## December 14, 2025 - INITIAL SUCCESS (ν=1 Case)

### iteration2 (c7732074)
- First serious attempt at ν=1 case
- **PROVEN:** tuza_base_case, triangleCoveringNumber_le_card_add_deleteEdges
- **PROVEN:** exists_max_packing, packing_one_implies_intersect, k4_tau_le_2

### iteration3 (beae6b6a)
- Completed k4_is_maximal_if_nu_1 lemma
- Key insight: Any triangle shares edge with K₄ triangles when ν=1

### iteration3_alt_SUCCESS (7f9d358e) ⭐
- **FULL PROOF of tuza_conjecture_nu_1: ν=1 → τ≤2**
- 400+ lines of Lean 4
- **MAJOR MILESTONE**

---

## December 15, 2025 - Full Conjecture & ν=2 Attempts

### FULL_v2 (ff11a2fe → 3236adf0)
- Attempted full τ ≤ 2ν
- **PROVEN:** tuza_base_case, packing_mono_deleteEdges
- FAILED: tuza_case_nu_1 (missing import)

### ν=2 case attempts (v1-v6)
- 91eb28ea: ERROR - "Unexpected axioms" (used axiom instead of sorry)
- f62d4c0a: v5 with case analysis on |T₁ ∩ T₂|
- 710c3ede: v6 with enhanced scaffolding

---

## December 16, 2025 - ν=2 Deep Dive

### Three parallel approaches
- approach1_blocking: Block structure analysis
- approach2_forbidden: Forbidden subgraph approach
- approach3_deletion: Edge deletion strategy

### Main branch (4610138e) ⭐
**9 building blocks PROVED:**
1. nu_eq_two_of_unique_edge
2. packing_intersects_unique_triangle_edges
3. nu_le_one_of_disjoint_T
4. covering_le_delete_add_card
5. nu_le_one_of_delete_other_edges
6. unique_edge_implies_tau_le_4
7. triangle_share_edge_implies_eq_or_intersect_eq_singleton
8. extension_triangle_exists_nu2 (KEY LEMMA!)
9. triangle_shares_edge_with_packing

---

## December 17, 2025 - Discovery Mode

### v8_forbidden (7a29e24c)
- Formal with complete building blocks

### discovery (d2598ba5)
- Free exploration mode

### informal (86e8ac29)
- Natural language proof walkthrough

---

## December 18, 2025 - Full Conjecture Push

### v4 (d50cf3fb / b4549d16)
**Date:** Dec 18, 2025 07:51 CST
- First full Tuza attempt
- Strong induction via 2-edge reduction
- **Result:** FAILED - reduction property not proven

### v5 (e900e161 / ef7e7f99)
**Date:** Dec 18, 2025 ~08:00 CST
- Fixed variable naming bug from v4
- **Result:** MAJOR DISCOVERY
  - Aristotle found **COUNTEREXAMPLE** to TuzaReductionProperty
  - Graph: Two triangles {0,1,2} and {0,1,3} sharing edge {0,1}
  - Proved 10+ helper lemmas with full proofs
  - Proved conditional theorem: "If reduction property, then Tuza"

### v6 (380fb7d3 / cca06048)
**Date:** Dec 18, 2025 14:29 CST
- Corrected approach: NearbyTriangles direct construction
- 160 lines prescriptive (detailed strategy hints)
- **Result:** SECOND COUNTEREXAMPLE
  - K₄ counterexample disproves this approach too
  - Each nearby triangle shares only ONE edge with packing
  - Formally proven: `two_edges_cover_nearby_counterexample`

### v7 (a64e90b3 / 085f46d5)
**Date:** Dec 18, 2025 14:34 CST
- **Boris pattern:** 47 lines minimal
- Just definitions + theorem statement, no hints
- **Result:** PARTIAL SUCCESS - BEST OUTCOME
  - **PROVEN:** τ ≤ 3ν (weak Tuza, full formal proof ~120 lines)
  - **PROVEN:** τ(K₄) = 2ν(K₄) - K₄ is tight
  - **PROVEN:** τ(K₅) = 2ν(K₅) - K₅ is tight
  - Full conjecture τ ≤ 2ν NOT proven (expected)

### v8 (21873a56 / 4828661f)
**Date:** Dec 18, 2025 14:49 CST
- Scaffolded: 7 proven lemmas as building blocks
- No strategic hints (Grok rated 9/10)
- **Result:** COMPLETED
  - **PROVEN:** τ ≤ 3ν (same as v7, different approach)
  - Created `TuzaContext` axiomatic class
  - Proved `packing_card_edges`, `max_packing_destroys_all_triangles`
  - Full Tuza τ ≤ 2ν NOT proven
  - Aristotle comment: "remains an open problem in mathematics"

---

## December 19, 2025 - CRITICAL DISCOVERIES (ν=2)

### v9 (9a636df7) ⭐⭐
**Date:** Dec 19, 2025
- Full robustified ν=2 submission (800 lines)
- **Result:** MAJOR PROOF SUCCESS
  - **PROVEN:** `exists_disjoint_in_K4` - THE KEY OUTLIER LEMMA!
  - Aristotle created helper: `k4_avoidance_helper` (in K₄, for any edge, ∃ 3-subset avoiding it)
  - This was one of the 3 gaps in ν=2 proof
  - Now only 2 gaps remain: `tau_gt_4_implies_two_K4`, `two_K4_cover_le_4`

### v10 minimal (3b80f616) ⭐⭐⭐
**Date:** Dec 19, 2025
- Minimal 200-line ν=2 attempt
- **Result:** CRITICAL COUNTEREXAMPLE FOUND
  - **NEGATED:** `two_K4_almost_disjoint` - THIS BREAKS THE PROOF STRATEGY!
  - **Counterexample:** Graph on 6 vertices (Fin 6)
    - T1 = {0, 1, 2}, T2 = {3, 4, 5} - edge-disjoint triangles
    - s1 = {0, 1, 2, 3} is K₄ containing T1
    - s2 = {0, 3, 4, 5} is K₄ containing T2
    - s1 ∩ s2 = {0, 3} has cardinality 2 > 1!
  - The lemma claimed |s1 ∩ s2| ≤ 1, but it can be 2

### Implications
**The current ν=2 proof strategy is fundamentally flawed:**
- We assumed K₄ extensions from edge-disjoint triangles would be "almost disjoint"
- Aristotle formally disproved this with concrete counterexample
- The "outlier argument" needs redesign
- Two edge-disjoint packing triangles CAN extend to K₄s sharing 2 vertices

### Current Status (Post-Counterexample)
**PROVEN (can reuse):**
1. `exists_max_packing` - max packing exists
2. `triangle_shares_edge_with_packing` - every triangle shares edge with packing
3. `extension_triangle_exists_nu2` - each edge has extension triangle
4. `extensions_form_K4` - packing triangles extend to K₄s when τ > 2ν
5. `tau_gt_4_implies_two_K4_with_packing` - get two K₄s with their triangles
6. `exists_disjoint_in_K4` - **NEW FROM v9** - outlier disjoint triangle exists

**FALSE (counterexampled):**
- `two_K4_almost_disjoint` - K₄s from edge-disjoint triangles need NOT be almost-disjoint

**STILL NEED:**
- New covering strategy that handles K₄s sharing 2 vertices
- `two_K4_cover_le_4` - must be reproven with different approach

---

## Key Events Summary

| Time | Event |
|------|-------|
| Dec 18, 07:51 | Initial v4 attempt with strong induction |
| Dec 18, ~12:00 | v5 output analyzed - counterexample discovered |
| Dec 18, 14:29 | v6 submitted with corrected approach |
| Dec 18, 14:34 | v7 (Boris pattern) submitted |
| Dec 18, ~16:00 | v6 output analyzed - SECOND counterexample |
| Dec 18, ~16:30 | v7 output analyzed - τ ≤ 3ν PROVEN |
| Dec 18, ~17:00 | Strategic decision: pivot from Tuza |
| Dec 18, ~18:00 | Full documentation created |
| Dec 19, ~?? | v9 proves `exists_disjoint_in_K4` (outlier lemma) |
| Dec 19, ~?? | v10 finds COUNTEREXAMPLE to `two_K4_almost_disjoint` - strategy broken |

## Lessons Encoded

1. **v4→v5:** Bug fixes matter - variable naming broke pattern matching
2. **v5 output:** Counterexamples are valuable discoveries, not failures
3. **v6 failure:** Prescriptive approaches can be systematically disproved
4. **v7 success:** Boris pattern (minimal intervention) works best
5. **Overall:** Let AI explore freely → proves what it CAN prove

## Files Created

| Version | Formal UUID | Informal UUID | Key File |
|---------|-------------|---------------|----------|
| v5 | e900e161 | ef7e7f99 | tuza_SUCCESS_conditional.lean |
| v6 | 380fb7d3 | cca06048 | tuza_COUNTEREXAMPLE_v6.lean |
| v7 | a64e90b3 | 085f46d5 | tuza_PROVEN_weak_bound.lean |
| v8 | 21873a56 | 4828661f | tuza_FULL_v8_scaffolded.lean |
