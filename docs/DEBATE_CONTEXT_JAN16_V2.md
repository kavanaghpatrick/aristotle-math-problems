# Comprehensive Debate Context: τ ≤ 8 for PATH_4

**Date**: January 16, 2026
**Goal**: Find correct proof strategy for τ ≤ 8 in PATH_4 case of Tuza's conjecture (ν = 4)

---

## THE PROBLEM

We need to prove: For any graph G with triangle packing number ν(G) = 4 in PATH_4 configuration, the triangle covering number τ(G) ≤ 8.

**PATH_4 Structure**:
```
A = {a1, a2, v1} —v1— B = {v1, b, v2} —v2— C = {v2, c, v3} —v3— D = {v3, d1, d2}
```
- Adjacent pairs share exactly one vertex: A∩B = {v1}, B∩C = {v2}, C∩D = {v3}
- Non-adjacent pairs are disjoint: A∩C = ∅, A∩D = ∅, B∩D = ∅

---

## WHAT WE KNOW IS TRUE (PROVEN)

### Aristotle-Verified Lemmas

| Slot | Lemma | Key Result |
|------|-------|------------|
| **382** | `tau_le_8_with_bridges` | **τ ≤ 8 WORKS on Fin 8 with 4 bridges!** Cover: {0,1},{1,2},{2,3},{3,4},{4,5},{5,6},{6,7},{7,0} |
| **412** | `not_all_three_edge_types` | At most 2 of 3 S_e edge types are nonempty (6-packing argument) |
| **422** | `exists_two_edges_cover_Se` | 2 edges adaptively cover all S_e externals |
| **441** | `bridge_contains_shared` | All bridges between E and F contain shared vertex v |
| **383** | `tau_le_8_from_partition` | If triangles partition into sets with τ ≤ 2 each, assembly works |
| **384** | `nu4_triangles_in_4_sets` | All triangles belong to ∪S_e (maximality) |

### Literature Lemmas (Validated)

- `tau_S_le_2`: τ(S_e) ≤ 2 for pure externals
- `tau_X_le_2`: τ(bridges) ≤ 2 per adjacent pair
- `avoiding_contains_base_edge`: Triangles avoiding v must share base edge
- `bridges_contain_shared_vertex`: All bridges contain the intersection vertex
- `Se_disjoint`: S_e sets are pairwise disjoint (for pure externals)
- `triangle_shares_edge_with_packing`: Every triangle shares edge with some M-element (maximality)

---

## WHAT WE KNOW IS FALSE (31 DISPROVEN LEMMAS)

### Critical False Lemmas Affecting This Proof

| # | Lemma | Why False | Impact |
|---|-------|-----------|--------|
| **31** | `bridge_auto_covered_by_pigeonhole` | Covering vertex v ≠ covering all triangles containing v | **THE CURRENT GAP** |
| **3** | `bridge_absorption` | Covering S_e doesn't automatically cover bridges | Bridges need explicit handling |
| **14** | `fan_apex_cover_all_sharing` | 2 edges per element don't cover all sharing triangles | Selection matters |
| **1** | `local_cover_le_2` | 2 M-edges at v insufficient for all triangles at v | Need right 2 edges |
| **29** | `sym2_cover_cardinality` | A.sym2 has 6 elements (includes self-loops), not 3 | Don't use A.sym2 for edge enumeration |
| **30** | `endpoint_D_external_contains_spine` | D-externals can avoid spine vertex v3 | Externals on base edge {d1,d2} |

### The Counterexample to Current Approach

```
Scenario: PATH_4 with A = {a1, a2, v1}, B = {v1, b, v2}

If adaptive S_e selection gives:
- C_A = {s(a1,a2), s(a2,v1)}  (avoiding empty S_e^{a1,v1})
- C_B = {s(v1,v2), s(b,v2)}   (avoiding empty S_e^{v1,b})

Bridge T = {v1, a1, b} has edges: s(v1,a1), s(v1,b), s(a1,b)
Neither C_A nor C_B contains any edge of T!
Result: Bridge T is NOT covered.
```

---

## THE KEY INSIGHT FROM slot382

**slot382 proves τ ≤ 8 works on a concrete graph with 4 bridges!**

The winning cover is NOT adaptive S_e selection. It's a **"boundary walking"** pattern:
```
Cover = {
  {0,1}, {1,2},   -- 2 edges from A, straddling shared vertex 2
  {2,3}, {3,4},   -- 2 edges from B, straddling shared vertex 4
  {4,5}, {5,6},   -- 2 edges from C, straddling shared vertex 6
  {6,7}, {7,0}    -- 2 edges from D, straddling shared vertex 0
}
```

**Why this works**:
- For A = {0,1,2} with shared vertex 2: edges {0,1} and {1,2}
- Edge {1,2} contains vertex 2 AND is an edge of bridge {1,2,4}
- The cover includes edges that "straddle" shared boundaries

---

## THE FUNDAMENTAL QUESTION

**Can we ALWAYS find 8 edges that cover everything (M + S_e + bridges)?**

Options to explore:
1. **Boundary-walking pattern**: Always use edges near shared vertices
2. **Coordinated selection**: Choose edges that complement neighbors
3. **Case analysis**: Different selection rules for different configurations
4. **Hybrid approach**: Adaptive for S_e, constrained for bridges

---

## STRUCTURAL CONSTRAINTS

### For Endpoints (A and D)

A = {a1, a2, v1} has one shared vertex v1.
- All A-B bridges contain v1 (proven)
- A's 3 edges: s(a1,v1), s(a2,v1), s(a1,a2)
- To hit ALL A-B bridges, need at least one of s(a1,v1), s(a2,v1)

**Key constraint**: If A has base-type externals (on {a1,a2}), must include s(a1,a2).
Then we have 1 edge left for spokes, hitting only SOME bridges.
But B can cover the missed bridges if B includes s(v1,b).

### For Middle Elements (B and C)

B = {v1, b, v2} has TWO shared vertices.
- A-B bridges contain v1
- B-C bridges contain v2
- B's 3 edges: s(v1,b), s(v1,v2), s(b,v2)

**The spine s(v1,v2) is special**: It contains BOTH shared vertices!
- Covers A-B bridges of form {v1, *, v2}
- Covers B-C bridges of form {v2, *, v1}

---

## QUESTIONS FOR DEBATE

1. **Is the boundary-walking pattern always valid?** Does it always give ≤ 8 edges?

2. **How to handle S_e externals with boundary-walking?** The pattern fixes edge choices, but S_e coverage needs adaptivity.

3. **Can we prove a coordination lemma?** Something like: "For any bridge T, at least one adjacent element's natural cover hits T"

4. **Is there a unified construction?** One that handles both S_e and bridges without case splits?

5. **Should we prove on Fin 8 first?** slot382 succeeded on Fin 8. Can we generalize?

---

## DEBATE RULES

- **Be rigorous**: Cite proven lemmas and known counterexamples
- **Be optimistic**: τ ≤ 8 IS achievable (slot382 proves it exists)
- **Explore alternatives**: Don't fixate on one approach
- **Check against false lemmas**: Before claiming something, verify it's not disproven
- **Goal**: Find a PROVABLE path, not just a plausible one

---

## AVAILABLE PROOF COMPONENTS

### For Assembly
- `tau_le_8_from_partition` (slot383): Union of ≤2 covers gives ≤8 total
- `covering_union_le_sum`: |Cover(A∪B)| ≤ |Cover(A)| + |Cover(B)|

### For S_e Coverage
- `not_all_three_edge_types` (slot412): At most 2 S_e types nonempty
- `exists_two_edges_cover_Se` (slot422): 2 edges suffice for S_e (adaptive)

### For Bridge Coverage
- `bridge_contains_shared` (slot441): Bridges contain intersection vertex
- `tau_le_8_with_bridges` (slot382): Proof exists on Fin 8

### For Structure
- `every_triangle_shares_edge_with_M`: Maximality gives decomposition
- `S_e_disjoint`: Pure externals don't overlap
