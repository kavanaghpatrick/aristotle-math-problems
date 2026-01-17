# Comprehensive Status: Tuza's Conjecture τ ≤ 2ν for ν = 4

**Date**: Jan 17, 2026
**Goal**: Prove τ(G) ≤ 8 for all graphs G with ν(G) = 4

---

## 1. THE CONJECTURE

**Tuza's Conjecture**: For any graph G, τ(G) ≤ 2ν(G), where:
- τ(G) = minimum number of edges needed to hit all triangles (triangle cover number)
- ν(G) = maximum number of edge-disjoint triangles (triangle packing number)

**Our target**: Prove τ ≤ 8 when ν = 4.

---

## 2. WHAT WE'VE PROVEN (Aristotle-verified, 0 sorry)

### 2.1 Concrete Instances on Fin 9

| Slot | Theorem | Description |
|------|---------|-------------|
| **447** | `tau_le_8_full_conflict` | τ ≤ 8 on Fin 9 with bridges + S_e externals |
| **450** | `tau_le_8`, `tau_eq_4` | τ ≤ 8 (actually = 4) on minimal PATH_4 graph |
| **382** | `tau_le_8` | τ ≤ 8 on graph with 4 bridge triangles |

### 2.2 Structural Lemmas (General, not Fin-specific)

| Slot | Theorem | Statement |
|------|---------|-----------|
| **448** | `bridge_not_in_Se` | Bridges are NOT S_e externals (share edge with 2 elements) |
| **448** | `bridge_has_external_edge` | Bridge {v,x,y} has edge {x,y} not in either adjacent element |
| **448** | `path4_bridge_bound` | Bridges only between adjacent PATH_4 elements |
| **441** | `bridge_contains_shared` | Bridge between E,F contains E∩F vertex |
| **434** | `endpoint_spokes_cover` | Endpoint A needs ≤2 edges (spokes) |
| **347** | `bridge_contains_shared_vertex` | Same as 441 |
| **347** | `middle_seam_covered` | Middle element seam coverage |
| **329** | `bridge_covered_by_selected_edges` | Bridges covered by apex-based selection |

### 2.3 Counting Lemmas

| Theorem | Bound |
|---------|-------|
| `tau_union_le_sum` | τ(A∪B) ≤ τ(A) + τ(B) |
| `tau_S_le_2` | τ(S_e) ≤ 2 for any element E |
| `tau_X_le_2` | τ(X_ef) ≤ 2 for adjacent pair |
| `externals_on_at_most_two_edges` | S_e uses ≤2 of E's 3 edges |

---

## 3. FALSE LEMMAS (Counterexamples found)

| # | Lemma | Why False | Impact |
|---|-------|-----------|--------|
| 6 | `external_share_common_vertex` | Externals of different elements don't share apex | König approach blocked |
| 8 | `link_graph_bipartite` | Link graph not bipartite | König matching blocked |
| 24 | `pairwise_Se_share_apex` | S_e externals don't share universal apex | Fan cover incomplete |
| 32 | `endpoint_adaptive_cover` | 6-packing implies missing edge | Endpoint needs fallback |
| **33** | `Se_third_vertex_outside` | On Fin 9, S_e externals don't need outside vertex | 5-packing argument needs revision |

---

## 4. THE PATH_4 STRUCTURE

```
A ——v1—— B ——v2—— C ——v3—— D
```

- A = {a1, a2, v1}, B = {v1, b, v2}, C = {v2, c, v3}, D = {v3, d1, d2}
- Adjacent pairs share exactly 1 vertex: A∩B={v1}, B∩C={v2}, C∩D={v3}
- Non-adjacent pairs are disjoint: A∩C=∅, A∩D=∅, B∩D=∅

### Triangle Categories

1. **Packing elements**: A, B, C, D (must be covered)
2. **S_e externals**: Share edge with ONE element, ≤1 vertex with others
3. **Bridges**: Share edge with TWO adjacent elements (NOT S_e!)
4. **X_ef triangles**: Share edge with non-adjacent pair (rare due to disjointness)

---

## 5. THE 2-EDGE-PER-ELEMENT STRATEGY

**Claim**: Each packing element contributes ≤2 edges to cover all triangles sharing an edge with it.

**For endpoints (A, D)**:
- Need to cover: A itself + S_e(A) externals
- Strategy: 2 spokes from shared vertex v1 (or v3 for D)
- Proven: `endpoint_spokes_cover`

**For middles (B, C)**:
- Need to cover: B itself + S_e(B) externals + potentially bridges
- Challenge: S_e(B) can force specific edge choices
- The "6-packing" constraint: At most 2 of 3 S_e types can be nonempty

**Total**: 4 elements × 2 edges = 8 edges maximum

---

## 6. THE BRIDGE PROBLEM

### What is a bridge?
A bridge between B and C is a triangle T = {v2, b', c'} where:
- b' ∈ B \ {v2} and c' ∈ C \ {v2}
- T shares edge {v2, b'} with B
- T shares edge {v2, c'} with C

### Why bridges are special
- Bridges are NOT S_e externals (they share edge with TWO elements)
- Bridges need coverage but aren't counted in S_e analysis
- Bridge can be covered by: {v2, b'}, {v2, c'}, or {b', c'}

### The "worst case" scenario (debated)
If both B and C are forced by their S_e externals to pick edges away from the bridge:
- B picks spine + left (away from v2-b')
- C picks spine + right (away from v2-c')
- Bridge T is uncovered!

### Round 3 Resolution Attempt
**Claim**: This scenario creates a 5-packing {A, D, T, E_B, E_C}, contradicting ν=4.

**Problem**: `Se_third_vertex_outside` was NEGATED on Fin 9. The 5-packing argument assumed S_e externals have a vertex outside the packing, which is false on Fin 9.

---

## 7. KEY INSIGHT: Fin 9 vs General Case

### On Fin 9
- All 9 vertices are in A∪B∪C∪D
- No "external" vertices exist
- S_e externals (if they exist) must reuse packing vertices
- slot447 proves τ ≤ 8 works via `native_decide`

### On Fin 10+
- At least one vertex outside the packing
- S_e externals CAN have truly external vertices
- The 5-packing argument might work here
- But we haven't proven it

---

## 8. FAILED APPROACHES

| Approach | Why Failed |
|----------|------------|
| König matching | Link graph not bipartite |
| Universal apex | S_e externals don't share common vertex |
| LP relaxation | Too complex for Lean formalization |
| Greedy cover | Doesn't respect edge-disjointness |
| Pure case analysis | Too many cases, Aristotle times out |

---

## 9. CURRENT GAPS

### Gap 1: General τ ≤ 8 theorem
We have τ ≤ 8 on specific Fin 9 graphs, not for all graphs with ν=4.

### Gap 2: Bridge coverage guarantee
We know bridges can be covered by {b', c'} edge, but haven't proven the counting works out (that adding bridge edges doesn't exceed 8 total).

### Gap 3: 5-packing argument on Fin 10+
The Round 3 insight (5-packing contradiction) needs to be proven for larger vertex sets where external vertices exist.

---

## 10. WHAT ARISTOTLE CAN DO

**Tier 1 (70-90% success)**: Counterexamples on Fin 5-7, decidable predicates
**Tier 2 (30-50% success)**: Subadditivity, simple induction, packing construction with 10+ scaffolding
**Tier 3 (10-20% success)**: Deep combinatorics requiring human-outlined proof structure
**Tier 4 (<5% success)**: Asymptotics, global coordination - AVOID

**Best approach**: Give Aristotle concrete Fin n instances with `native_decide`, or well-scaffolded general lemmas.

---

## 11. DATABASE STATISTICS

- **Total submissions**: 450+
- **Proven (0 sorry)**: ~50
- **Near-misses (1 sorry)**: ~30
- **False lemmas discovered**: 33
- **Failed approaches documented**: 38

---

## 12. QUESTIONS FOR DEBATE

1. **How do we generalize from Fin 9 to arbitrary graphs?**
   - Is there a reduction argument?
   - Can we prove a "worst case" is always Fin 9-like?

2. **Is the 5-packing argument salvageable?**
   - Does it work on Fin 10+?
   - Is there an alternative constraint from ν=4?

3. **Should we try a different proof structure?**
   - Induction on number of triangles?
   - Case analysis by intersection pattern?
   - Probabilistic/counting argument?

4. **What concrete next submission would make progress?**
   - Prove 5-packing on Fin 10?
   - Prove bridge counting lemma?
   - Try a different PATH_4 case (cycle, star)?

---

## 13. PROVEN SCAFFOLDING AVAILABLE

```lean
-- From slot448 (all proven)
theorem bridge_not_in_Se
theorem bridge_has_external_edge
theorem path4_bridge_bound

-- From slot447 (all proven on Fin 9)
theorem Se_C_spine_empty
theorem tau_le_8_full_conflict
theorem full_conflict_nu_eq_4

-- From slot434 (all proven)
theorem endpoint_spokes_cover
theorem endpoint_two_edges_suffice

-- From various slots
theorem tau_union_le_sum
theorem tau_S_le_2
theorem externals_on_at_most_two_edges
theorem bridge_contains_shared_vertex
```

This scaffolding can be included in new submissions to boost success rate.
