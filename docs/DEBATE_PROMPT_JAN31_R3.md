# Tuza ν=4 Multi-Agent Debate - January 31, 2026
## Three-Round Debate: Grok, Gemini, Codex

---

## MISSION

Prove Tuza's conjecture τ(G) ≤ 2ν(G) for the case ν=4, meaning **τ ≤ 8**.

---

## CURRENT STATUS SUMMARY

| Case | Status | τ Bound | Notes |
|------|--------|---------|-------|
| path_4 | ✅ Complete (concrete) | τ ≤ 8 | 107 theorems on Fin n, not general |
| cycle_4 | Partial | τ ≤ 12 | τ ≤ 8 needs fan apex work |
| star_all_4 | Partial | τ ≤ 12 | 2 sorries in tau_le_8_triple_apex |
| three_share_v | Partial | τ ≤ 12 | 2 sorries in tau_le_8_triple_apex |
| scattered | Partial | τ ≤ 12 | tau bound has sorry |
| two_two_vw | Partial | τ ≤ 12 | Needs tightening |
| matching_2 | Partial | τ ≤ 12 | Same as two_two_vw |

---

## VALIDATED TRUE LEMMAS (Safe to Use)

### Core Structural Lemmas
| Lemma | Statement | Status |
|-------|-----------|--------|
| `tau_S_le_2` | τ(S_e) ≤ 2 for exclusive externals | ✅ Proven |
| `tau_X_le_2` | τ(X_ef) ≤ 2 for bridges | ✅ Proven |
| `tau_pair_le_6` | τ(T_pair) ≤ 6 (4 spokes + 2 bases) | ✅ Proven |
| `tau_union_le_sum` | τ(A ∪ B) ≤ τ(A) + τ(B) | ✅ Proven |

### S_e Structure Lemmas
| Lemma | Statement |
|-------|-----------|
| `S_e_pairwise_intersect` | Any two triangles in S_e share ≥2 vertices |
| `S_e_structure` | S_e has common edge OR common external vertex |
| `Se_disjoint` | S_e sets are pairwise disjoint for distinct packing elements |
| `different_edges_share_external_vertex` | Externals using different edges of same M-element share external vertex |

### Bridge Lemmas
| Lemma | Statement |
|-------|-----------|
| `bridges_contain_v` | Bridges X(e,f) all contain shared vertex v |
| `bridge_contains_shared_vertex` | Bridge between adjacent M-elements contains their shared vertex |
| `X_ef_empty_of_disjoint` | X(e,f) = ∅ when e ∩ f = ∅ (no bridges between disjoint elements) |
| `Te_eq_Se_union_bridges` | T_e = S_e ∪ bridges(e) decomposition |

### Triangle Classification
| Lemma | Statement |
|-------|-----------|
| `triangle_shares_edge_with_packing` | Every triangle shares edge with some M-element (maximality) |
| `avoiding_contains_base_edge` | Triangles avoiding v must share base edge {a,b}, not spokes |

### Covering Bounds
| Lemma | Statement |
|-------|-----------|
| `tau_containing_v_in_pair_le_4` | τ(containing v in T_pair) ≤ 4 (4 spokes) |
| `tau_avoiding_v_in_pair_le_2` | τ(avoiding v in T_pair) ≤ 2 (2 base edges) |
| `covering_number_on_le_two_of_subset_four` | Triangles on ≤4 vertices have τ ≤ 2 |

---

## FALSE LEMMAS (Do NOT Use)

### 🔴 Aristotle-Verified (Highest Confidence)
| Lemma | Why False | Counterexample |
|-------|-----------|----------------|
| `two_externals_share_edge` | Externals can share just 1 vertex | T₁={0,1,7}, T₂={1,2,8} share only vertex 1 |
| `Se_fan_apex` | Externals don't share common apex | 3 externals on K4 where each pair shares different vertex |
| `at_most_two_edge_types` | Bridges can use any edge-type | K4 + path has all 3 types |
| `bridge_absorption` | S_e cover doesn't auto-cover bridges | Cover {{1,2},{3,4}} misses bridge {0,1,3} |
| `sym2_cover_cardinality` | Finset.sym2 includes self-loops | t.sym2 has 6 elements, not 3 |
| `triangle_sym2_card_3` | Self-loops s(v,v) included | {0,1,2}.sym2 = 6 elements |
| `triangles_at_vertex_cover_le_2` | 3+ triangles at v can need 3+ edges | {0,1,2}, {0,3,4}, {0,5,6} need 3 edges |
| `not_all_three_types_Se` | K4 has externals on all 3 edges | K4 + path counterexample |
| `five_packing_from_K4_externals` | K4 externals share 2 vertices | |

### 🟠 AI-Verified (High Confidence)
| Lemma | Why False |
|-------|-----------|
| `external_share_common_vertex` | Externals from different M-elements share only v |
| `fan_apex_outside_A` | "Book" case has apex IN A, not outside |
| `local_cover_le_2` | 4 triangles at v can need 4 edges |
| `externals_on_at_most_two_edges` | K4 allows externals on all 3 edges |
| `fan_apex_cover_all_sharing` | Doesn't cover bridges |
| `tau_S_union_X_le_2` | S_e ∪ X_ef can need 3 edges |

### ⚪ Trivially False
| Lemma | Why False |
|-------|-----------|
| `avoiding_covered_by_spokes` | Spokes contain v, avoiding triangles don't |
| `tau_pair_le_4` | Need 6 edges (4 spokes + 2 bases), not 4 |

---

## KEY COUNTEREXAMPLES

### 1. Octahedron (K4-free but all 3 edge-types)
```
Vertices: 0-5
Edges: 12 total (octahedron graph)
Packing M = {{0,1,2}, {1,3,4}, {2,4,5}, {0,3,5}}

Triangle e = {0,1,2} has externals on ALL 3 edges:
  - {0,1,3} uses vertex 3
  - {1,2,4} uses vertex 4
  - {0,2,5} uses vertex 5

τ ≤ 8 VERIFIED: Cover = {(0,1), (0,2), (0,3), (0,5), (1,4), (2,4), (3,4), (4,5)}
```

### 2. K4 Externals (5-packing fails)
```
K4 on {0,1,2,3} + path triangles {4,5,6}, {6,7,8}, {8,9,10}
M = {{0,1,2}, {4,5,6}, {6,7,8}, {8,9,10}}

Externals of {0,1,2}: {0,1,3}, {1,2,3}, {0,2,3}
All share vertex 3 (the K4 apex)
5-packing fails because externals share 2 vertices
```

### 3. Externals Share Only Vertex (not edge)
```
M = {A={0,1,2}, B={0,3,4}, C={3,7,8}, D={7,1,9}}

A-externals:
  T₁ = {0,1,7}
  T₂ = {1,2,8}

T₁ ∩ T₂ = {1} ← Only 1 vertex, NOT an edge
```

---

## FAILED PROOF STRATEGIES

1. **K4-free split** - Octahedron breaks this (K4-free but has all 3 types)
2. **tau_pair_le_4** - Correct bound is 6, not 4
3. **externals_share_edge** - They can share just 1 vertex
4. **fan_apex_outside_A** - "Book" case has apex inside A
5. **link_graph_bipartite** - Link graphs can have odd cycles
6. **bridge_absorption** - Bridges need explicit handling
7. **sym2 edge enumeration** - Includes self-loops

---

## WHAT ACTUALLY WORKS

### PATH_4 Success Pattern (107 theorems)
- Case split: no bridges / 1 external / 2 externals
- Case 2b (2 externals) leads to ν≥5, impossible
- Explicit cover construction for Cases 1 and 2a
- Uses `native_decide` on Fin n

### Proven Decomposition
```
T_pair(e,f) = containing(v) ∪ avoiding(v)
τ(containing v) ≤ 4  (4 spokes)
τ(avoiding v) ≤ 2    (2 base edges)
τ(T_pair) ≤ 6
```

### Valid Cover Construction
For 4-packing M = {A, B, C, D}:
- Each S_e: ≤2 edges (tau_S_le_2)
- Each X_ef: ≤2 edges (tau_X_le_2)
- Total by subadditivity: ≤8 edges (if overlaps exist)

---

## DEBATE QUESTIONS

### Round 1: Strategy Selection
Given all true/false lemmas above, what is the correct path to complete τ≤8?
- Which remaining cases should we prioritize?
- What new lemmas do we need?
- How do we handle the octahedron/K4 cases?

### Round 2: Technical Details
- What is the correct formulation of "fan apex" that works for both internal and external apex?
- How do we ensure cover overlaps give τ≤8 instead of τ≤12?
- Can we unify the case handling?

### Round 3: Implementation
- What concrete Lean files should we create?
- What hypotheses are needed for Aristotle success (Tier 1-2)?
- What order should we submit proofs?

---

## CONSTRAINTS

### Aristotle Capabilities
- **Tier 1 (70-90%)**: Counterexamples on Fin 5-7, decidable predicates
- **Tier 2 (30-50%)**: Simple induction, LP witnesses, packing construction
- **Tier 3 (10-20%)**: Deep combinatorics with human outline
- **Tier 4 (<5%)**: Avoid entirely

### Lean/Mathlib
- Use `SimpleGraph V` for general theorems
- Use `Fin n` for concrete validation
- Avoid `Finset.sym2` for edge enumeration (self-loops)

### What We Need
- General theorem: ∀G with ν(G)=4, τ(G)≤8
- Not just concrete instances on Fin n
- Must handle all 7 cases or prove unified bound
