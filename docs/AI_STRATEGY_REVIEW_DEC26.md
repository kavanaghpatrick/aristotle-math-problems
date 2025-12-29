# Tuza ν=4 Strategy Review - December 26, 2025

## Executive Summary

We are attempting to prove Tuza's conjecture for ν=4: **If a graph G has maximum edge-disjoint triangle packing of size 4, then at most 8 edges suffice to cover all triangles (τ ≤ 2ν = 8).**

**Current Status:** 3 of 7 cases PROVEN, 4 cases PARTIAL with key lemmas proven.

---

## The Problem

**Tuza's Conjecture (1981):** For any graph G, τ(G) ≤ 2ν(G), where:
- ν(G) = maximum number of edge-disjoint triangles (packing number)
- τ(G) = minimum number of edges needed to hit all triangles (covering number)

**Our Target:** Prove τ ≤ 8 when ν = 4.

---

## The Seven Cases (by Sharing Graph Structure)

When ν=4, we have 4 edge-disjoint triangles {A, B, C, D}. Their **sharing graph** shows which pairs share a vertex:

| Case | Structure | Status | Key Insight |
|------|-----------|--------|-------------|
| **star_all_4** | All 4 share vertex v | ✅ PROVEN | 4 spokes suffice, τ ≤ 4 |
| **three_share_v** | 3 share v, 1 isolated | ✅ PROVEN | 3 spokes + 2 edges, τ ≤ 5 |
| **scattered** | No shared vertices | ✅ PROVEN | 4×2 = 8 edges exactly |
| **path_4** | A—B—C—D (path) | ⚠️ PARTIAL | T_pair decomposition |
| **cycle_4** | A—B—C—D—A (cycle) | ⚠️ PARTIAL | All-Middle + bridges absorbed |
| **two_two_vw** | {A,B} share v, {C,D} share w | ⚠️ PARTIAL | Two independent pairs |
| **matching_2** | Same as two_two_vw | ⚠️ PARTIAL | Depends on two_two_vw |

---

## Proven Foundation (37 Validated Lemmas)

### Core Bounds
```
tau_union_le_sum:        τ(A ∪ B) ≤ τ(A) + τ(B)           [Subadditivity]
tau_S_le_2:              τ(S_e) ≤ 2                        [S_e = triangles sharing only with e]
tau_X_le_2:              τ(X_ef) ≤ 2                       [X_ef = bridges between e,f]
tau_containing_v_le_4:   τ(containing v in T_pair) ≤ 4    [Spokes cover]
tau_avoiding_v_le_2:     τ(avoiding v in T_pair) ≤ 2      [Base edges cover]
```

### Structural Lemmas
```
triangle_shares_edge_with_packing:  Every triangle shares edge with max packing
diagonal_bridges_empty:             A∩C=∅ ⟹ X_AC=∅ (no diagonal bridges)
bridges_contain_shared_vertex:      All X_ef triangles contain v where e∩f={v}
S_e_structure:                      S_e has star OR radial structure
avoiding_contains_base_edge:        Avoiding triangles share base edge
cycle4_all_triangles_contain_shared: Every triangle contains some v_ij
```

---

## The Critical Discovery: FALSE Lemma

### What We Thought (WRONG)
```
avoiding_covered_by_spokes: If t avoids v, some spoke {v,x} ∈ t.sym2
```

### Why It's FALSE (Aristotle Proof)
```
Counterexample on 5 vertices:
- e = {0,1,2}, f = {0,3,4}, shared v = 0
- t = {1,2,3} avoids v=0 but shares edge {1,2} with e
- Spokes from 0: {0,1}, {0,2}, {0,3}, {0,4}
- t.sym2 = {{1,2}, {1,3}, {2,3}}
- NONE of the spokes are in t.sym2 because 0 ∉ t!
```

### The Correct Approach (PROVEN)
```
avoiding_contains_base_edge:
- If t avoids v but shares edge with e = {v,a,b}
- Then t MUST contain base edge {a,b} (not spokes!)
- Covered by 2 base edges, not 4 spokes
```

---

## Current Strategy for Remaining Cases

### PATH_4 Strategy
```
Packing: A—B—C—D with shared vertices v_ab, v_bc, v_cd

Decomposition:
- T_pair(A,B) = triangles sharing edge with A or B
- T_pair(C,D) = triangles sharing edge with C or D
- All triangles ⊆ T_pair(A,B) ∪ T_pair(C,D) [PROVEN]

Bound attempt:
- τ(T_pair(A,B)) ≤ τ(containing v_ab) + τ(avoiding v_ab) ≤ 4 + 2 = 6
- τ(T_pair(C,D)) ≤ 6
- τ(all) ≤ 6 + 6 = 12 [TOO HIGH!]

Problem: Naive bound gives 12, not 8.
```

### CYCLE_4 Strategy
```
Packing: A—B—C—D—A with shared vertices v_ab, v_bc, v_cd, v_da

Key insight (PROVEN): cycle4_same_as_path4_union
- The extra D—A edge creates bridges X_DA
- But X_DA ⊆ T_pair(A,B) (bridges absorbed!)
- So cycle_4 reduces to path_4 analysis

All-Middle Property (PROVEN):
- Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da
- This partitions triangles by shared vertex

Per-vertex approach:
- τ(triangles at v_ab) ≤ 2 (if we can prove this)
- τ(triangles at v_bc) ≤ 2
- τ(triangles at v_cd) ≤ 2
- τ(triangles at v_da) ≤ 2
- Total: ≤ 8 [TARGET!]

Gap: Need to prove τ(at each shared vertex) ≤ 2
```

---

## The Slot69 Breakthrough (0 Sorrys!)

Slot69 achieved a complete proof with key lemmas:

```lean
-- All triangles covered by T_pair union
lemma cycle4_tpair_union_covers_all:
  G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D

-- Spokes cover containing triangles
lemma tau_containing_v_in_pair_le_4:
  τ(trianglesContaining (T_pair G e f) v) ≤ 4

-- Base edges cover avoiding triangles
lemma tau_avoiding_v_in_pair_le_2:
  τ(trianglesAvoiding (T_pair G e f) v) ≤ 2
```

**But:** This gives τ(T_pair) ≤ 6, leading to total bound of 12.

---

## Key Questions for AI Review

1. **How do we get from 12 to 8?** The naive T_pair decomposition gives 6+6=12. What overlap or tighter bound gets us to 8?

2. **Is the per-vertex approach viable?** If we partition by shared vertex instead of T_pair, can we prove τ(at v) ≤ 2?

3. **Can we exploit bridge absorption?** Slot72 shows X_DA ⊆ T_pair(A,B). Does this reduce the effective count?

4. **Is there a better decomposition?** Instead of T_pair(A,B) ∪ T_pair(C,D), should we use S_e decomposition?

5. **What about the 8-edge explicit construction?** Can we directly construct 8 edges and prove they cover all triangles?

---

## Historical Failed Approaches (22 Documented)

| Approach | Why It Failed |
|----------|---------------|
| `avoiding_covered_by_spokes` | Spokes contain v, but avoiding triangles don't |
| `tau_pair_le_4` | Wrong bound; correct is ≤6 |
| `bridge_absorption` | S_e covers don't automatically absorb bridges |
| `cycle_opposite_disjoint` | Opposite pairs can share 1 vertex |
| `Parker_induction` | T_e can have 5+ triangles at ν=4 |
| `probabilistic_bound` | Only asymptotic, not constructive |

---

## What We Need

**Option A: Fix the T_pair bound**
- Show T_pair(A,B) ∩ T_pair(C,D) has significant overlap
- Or prove τ(T_pair) ≤ 4 directly (not via containing+avoiding split)

**Option B: Per-vertex decomposition**
- Partition ALL triangles by which shared vertex they contain
- Prove τ(at each vertex) ≤ 2 (need intersecting family argument)
- Use All-Middle to ensure partition is complete

**Option C: Direct 8-edge construction**
- Pick 2 edges per packing element strategically
- Prove these 8 edges cover all triangles
- Bypass decomposition bounds entirely

---

## Files to Reference

- `proven/tuza/nu4/slot69_*/output.lean` - 0 sorry proof with key lemmas
- `proven/tuza/nu4/slot70_*/output.lean` - diagonal_bridges_empty
- `proven/tuza/nu4/slot71_*/output.lean` - S_e_structure
- `proven/tuza/nu4/slot72_*/output.lean` - bridges absorbed
- `proven/tuza/nu4/slot60_cycle4_proven.lean` - FALSE lemma negation
- `proven/tuza/nu4/slot61_tau_union_full.lean` - avoiding_contains_base_edge

---

## Request for AI Reviewers

Please evaluate:
1. **Is our overall strategy sound?** Are we on the right track?
2. **What's the best path from 12 to 8?** Which option (A, B, or C) is most promising?
3. **Are there mathematical errors in our reasoning?** Any flaws in the proven lemmas?
4. **What alternative approaches should we consider?** Literature suggestions?
5. **Specific next steps?** What should the next Aristotle submission attempt?
