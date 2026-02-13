# Tuza ν=4: Corrected Strategic Summary
## February 2, 2026 (Post-Audit)

**CRITICAL CORRECTION**: The previous debate incorrectly recommended cycle_4 as "easiest, priority #1".
The 20-agent database audit revealed cycle_4 is actually the **MOST BLOCKED** case with 4 false lemmas and 10 failed approaches.

---

## PART 1: VERIFIED CASE STATUS

### Phase 1 vs Phase 2 Distinction

| Phase | Description | What's Proven |
|-------|-------------|---------------|
| **Phase 1** | MINIMAL graph: only M-triangle edges, `trianglesInG = M` | τ ≤ 4 for all cases |
| **Phase 2** | GENERAL graph: arbitrary edges, externals + bridges exist | Only 3 cases complete |

### Complete Case Inventory

| Case | Phase 1 (Minimal) | Phase 2 (General) | Key File | Blockers |
|------|-------------------|-------------------|----------|----------|
| **star_all_4** | ✅ τ = 4 | ✅ COMPLETE | slot49 | None - no externals possible |
| **three_share_v** | ✅ τ ≤ 4 | ✅ COMPLETE | slot50 | None - no externals possible |
| **path_4** | ✅ τ ≤ 4 | ✅ COMPLETE | slot451-453 | None - 107 theorems proven |
| **scattered** | ✅ τ ≤ 4 | ❓ UNCLEAR | slot376 | May need Phase 2 work |
| **two_two_vw** | ✅ τ ≤ 4 | ❌ PARTIAL | slot379 | `no_inter_pair_bridges` |
| **matching_2** | ✅ τ ≤ 4 | ❌ PARTIAL | - | Same as two_two_vw |
| **cycle_4** | ✅ τ ≤ 4 | 🔴 **BLOCKED** | slot377 | 4 false lemmas, 10 failed approaches |

---

## PART 2: WHY CYCLE_4 IS BLOCKED (NOT "EASIEST")

### 4 False Lemmas Blocking cycle_4

| ID | Lemma | Evidence | Impact |
|----|-------|----------|--------|
| 5 | `support_sunflower_tau_2` | Reasoning | 2 edges at shared vertex insufficient |
| 7 | `external_share_common_vertex` | AI verified | Externals from A vs B don't share apex - **MAJOR BLOCKER** |
| 8 | `link_graph_bipartite` | AI verified | **König theorem INVALID** for link graphs |
| 10 | `krivelevich_bound_forall_w` | Aristotle | LP bound uses supremum, not any w |

### 10 Failed Approaches for cycle_4

| ID | Approach | Why Failed |
|----|----------|------------|
| 8 | cycle_opposite_disjoint | Opposite pairs share vertices |
| 27 | cycle4_missing_distinctness_axioms | Need explicit v_ab ≠ v_bc axioms |
| 30 | slot110_output_analysis | tau_le_8_cycle4 NOT proven despite claims |
| 36 | slot146_combined_link_cover_2 | König requires bipartiteness |
| 37 | link_graph_bipartite | M-neighbors form odd cycles |
| 39 | konig_lite_case_analysis | Blocked by bipartiteness failure |
| 40 | lp_relaxation_krivelevich | LP machinery too complex |
| 41 | constructive_cover_bipartite | Useless without bipartiteness |
| + 2 more | ... | ... |

### Structural Reason cycle_4 is Hard

- **path_4**: Has endpoints (degree 1) enabling decomposition
- **cycle_4**: No endpoints (all degree 2), symmetric structure resists decomposition

---

## PART 3: CORRECTED PRIORITY ORDER

Based on actual database state:

| Priority | Case | Reason |
|----------|------|--------|
| **1** | two_two_vw | Pairs are vertex-disjoint, simpler structure |
| **2** | matching_2 | Same as two_two_vw after it's solved |
| **3** | scattered (general) | May already be done if externals impossible |
| **4 (LAST)** | cycle_4 | Most blocked, 4 false lemmas, 10 failed approaches |

---

## PART 4: TODAY'S RESULTS

### Aristotle Submissions

| Slot | Result | Key Finding |
|------|--------|-------------|
| slot49 | ✅ 0 sorry | star_all_4 τ = 4 PROVEN |
| slot50 | ✅ 0 sorry | three_share_v τ ≤ 4 PROVEN |
| slot51 | 1 sorry | Selection argument missing, scaffolding proven |
| **slot52** | **Main theorem PROVEN** | `base_edges_cover_avoiding` verified |
| slot53 | In progress | triple_apex still processing |

### slot52 Victory

The main theorem `base_edges_cover_avoiding` is **FULLY PROVEN** by Aristotle:
- Shows τ(trianglesAvoiding G v) ≤ 4
- Only a helper lemma `cover_mono` (not needed for main proof) has sorry
- This is a key building block for τ ≤ 8

---

## PART 5: 39 FALSE LEMMAS SUMMARY

### By Evidence Level

| Level | Count | Confidence |
|-------|-------|------------|
| aristotle_verified | 23 | Definitive counterexample |
| ai_verified | 11 | High (multi-agent consensus) |
| reasoning_based | 3 | Medium |
| trivially_false | 2 | Obvious logical error |

### Critical False Lemmas (Never Use These)

| Lemma | Impact |
|-------|--------|
| `not_all_three_types` | K4 allows all 3 edge-types with externals |
| `Se_fan_apex` | Externals don't share common apex |
| `triangle_in_some_Se_or_M` | Bridges excluded from all S_e |
| `sym2_cover_cardinality` | NEVER use A.sym2 for edges |
| `covering_selection_exists` | Can't always select |M| covering edges |
| `bridge_absorption` | S_e cover doesn't absorb bridges |

---

## PART 6: PROVEN BUILDING BLOCKS

### Core True Lemmas (Use These)

| Lemma | Statement |
|-------|-----------|
| `tau_S_le_2` | τ(S_e) ≤ 2 for exclusive externals |
| `tau_X_le_2` | τ(X_{e,f}) ≤ 2 for bridges |
| `bridge_shares_with_le_2` | Bridges share with ≤2 M-elements |
| `tau_pair_le_6` | τ(T_pair) ≤ 6 (NOT 4!) |
| `avoiding_contains_base_edge` | Avoiding triangles share base edge |
| `triangle_shares_edge_with_packing` | Maximality lemma |

### Today's New Proofs

| Lemma | File |
|-------|------|
| `base_edges_cover_avoiding` | slot52 |
| `allSpokesFromM_covers` | slot51 |
| `tau_equals_nu` (star_all_4) | slot49 |
| `tuza_bound_three_share_v` | slot50 |

---

## PART 7: RECOMMENDED NEXT ACTIONS

### Immediate (This Week)

1. **Submit two_two_vw concrete construction**
   - Pairs are vertex-disjoint
   - Should eliminate inter-pair bridges
   - Follow slot49/50 pattern on Fin 10

2. **Check if scattered general case is trivial**
   - If M-elements are pairwise vertex-disjoint, no externals exist
   - May already be covered by slot376

3. **Work slot51 near-miss**
   - 1 sorry remaining (selection argument)
   - All scaffolding proven

### Avoid

- **DO NOT prioritize cycle_4** - most blocked case
- **DO NOT use any of the 39 false lemmas**
- **DO NOT use `Finset.sym2` for edge enumeration**

---

## PART 8: OPEN QUESTIONS FOR DEBATE

1. **Is scattered general case trivial?**
   - In scattered, M-elements are pairwise vertex-disjoint
   - Does this mean no external triangles can exist?

2. **two_two_vw: How hard is `no_inter_pair_bridges`?**
   - The pairs {A,B} and {C,D} share no vertices
   - Should bridges between pairs be impossible?

3. **Should we attempt cycle_4 general at all?**
   - 4 false lemmas, 10 failed approaches
   - Maybe accept τ ≤ 12 for cycle_4?

4. **What about K4 special handling?**
   - K4 breaks most lemmas
   - Should we split K4-containing vs K4-free?

---

## APPENDIX: Key File Locations

| Purpose | File |
|---------|------|
| Tracking database | `submissions/tracking.db` |
| star_all_4 proof | `submissions/nu4_final/slot49_star_all_4_clean_aristotle.lean` |
| three_share_v proof | `submissions/nu4_final/slot50_three_share_v_clean_aristotle.lean` |
| scattered minimal | `submissions/nu4_final/slot376_scattered_tau_le_4.lean` |
| cycle_4 minimal | `submissions/nu4_final/slot377_cycle4_tau_le_4.lean` |
| path_4 complete | `submissions/nu4_final/slot451-453*.lean` |
| Assembly | `submissions/nu4_final/slot454_tuza_nu4_assembly_v2.lean` |

---

*Document created after 20-agent database audit correcting previous debate errors.*
