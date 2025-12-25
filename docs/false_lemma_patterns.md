# False Lemma Patterns in Tuza ν=4 Proof Attempts

**Created**: 2025-12-25
**Purpose**: Document patterns of mathematically false lemmas to prevent future repetition

---

## The Critical Discovery

On 2025-12-25, an AI debate (Grok-4 + Gemini + Codex) discovered that `avoiding_covered_by_spokes` - a lemma used in slots 35, 57, 59, and 60 - is **mathematically false**.

### The False Lemma

```lean
lemma avoiding_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ trianglesAvoiding (T_pair G e f) v)
    (h_overlap : ∃ x ∈ t, x ∈ (e ∪ f) \ {v}) :
    ∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
  sorry  -- IMPOSSIBLE TO PROVE
```

### Proof of Falsity

```
Let t ∈ trianglesAvoiding(T_pair G e f) v, meaning v ∉ t.
Let spoke = {v, x} for any x ∈ (e ∪ f) \ {v}.
Claim: spoke ∈ t.sym2 (i.e., spoke is an edge of t)

For spoke ∈ t.sym2, we need both v ∈ t AND x ∈ t.
But t avoids v, so v ∉ t.
Therefore spoke ∉ t.sym2. □

The lemma claims ∃ spoke, spoke ∈ t.sym2, which is impossible.
```

**Root Cause**: TYPE ERROR - confusing vertex membership with edge membership.

---

## Pattern Categories

Analysis of 17 "wrong_direction" failures reveals these patterns:

### 1. Avoiding/Spoke Confusion (2 instances)
- `avoiding_covered_by_spokes` - Spokes contain v, but avoiding triangles exclude v
- `tau_pair_le_4_via_spokes` - Same error, different formulation

**Rule**: If `t` avoids `v`, then NO edge of `t` contains `v`. Don't claim spokes cover avoiding triangles.

### 2. Bridge Coverage Errors (5 instances)
- `bridge_absorption` - Cover of S_e ∪ S_f doesn't cover bridges
- `bridge_hit_by_Se_cover` - S_e cover misses bridges
- `bridges_absorbed_by_Se_cover` - Same pattern
- `bridge_outer_vertex_unique` - Bridges can share multiple vertices
- `bridges_inter_card_eq_one` - Bridges can share 2 vertices

**Rule**: Bridges between e and f are NOT automatically covered by covers of S_e or S_f. They need separate treatment.

### 3. Intersection Assumptions (2 instances)
- `cycle_opposite_disjoint` - Opposite pairs in cycle CAN share vertices
- `path_nonadjacent_disjoint` - Non-adjacent pairs CAN share vertices (when path is actually a cycle)

**Rule**: Don't assume non-adjacent elements are vertex-disjoint. Check the actual graph structure.

### 4. Vertex vs Edge Cover Confusion (1 instance)
- `vertex_cover_implies_bridge_cover` - Hitting all vertices of e doesn't mean covering bridges

**Rule**: Vertex covers and edge covers are different. An edge cover needs edges IN the triangle, not just incident to its vertices.

### 5. Over-optimistic Bounds (7 instances)
- `tau_containing_vertex_le_2` - Wrong: can need more than 2 edges
- `containing_v_cover with τ ≤ 2` - Wrong for general case
- Various induction attempts that don't preserve bounds

**Rule**: Verify bounds with concrete examples before assuming they hold.

---

## Validated vs Unvalidated Lemmas

As of 2025-12-25:
- **62 lemmas** marked as "proven" but NOT validated for mathematical truth
- **8 lemmas** validated as mathematically TRUE:
  1. `tau_containing_v_in_pair_le_4` - Spokes cover containing triangles
  2. `tau_avoiding_v_in_pair_le_2` - Base edges cover avoiding triangles
  3. `avoiding_contains_base_edge` - Avoiding must share base edge
  4. `tau_union_le_sum` - Subadditivity of covering number
  5. `tau_v_decomposition` - Decomposition by vertex containment
  6. `tau_S_le_2` - Se triangles covered by 2 edges
  7. `tau_X_le_2` - Bridge triangles covered by 2 edges
  8. `triangle_shares_edge_with_packing` - Maximality implies edge sharing

---

## Prevention Checklist

Before submitting a lemma to Aristotle:

1. **Type Check**: Does the conclusion make type-sense?
   - If claiming `edge ∈ triangle.sym2`, verify both endpoints are in the triangle
   - If claiming `v ∈ t` for avoiding t, STOP - contradiction

2. **Boundary Check**: Does the claim hold at boundaries?
   - Empty sets
   - Singleton sets
   - Maximum cardinality cases

3. **Counterexample Search**: Try to falsify on small graphs
   - 3 vertices (single triangle)
   - 5 vertices (two sharing triangles)
   - 6 vertices (path of 3 triangles)

4. **Aristotle Counterexample History**: Check failed_approaches table
   ```sql
   SELECT approach_name, why_failed FROM failed_approaches
   WHERE frontier_id = 'nu_4' AND failure_category = 'wrong_direction';
   ```

5. **Pattern Match**: Does this resemble a known false pattern?
   - "X covers avoiding triangles" where X contains excluded vertex
   - "Cover of S covers bridges"
   - "Non-adjacent implies disjoint"

---

## The Correct Approach for T_pair

Given e = {v, a, b} and f = {v, c, d} sharing exactly vertex v:

**Triangles containing v**:
- Covered by 4 spokes: {v,a}, {v,b}, {v,c}, {v,d}
- τ(containing) ≤ 4 ✓

**Triangles avoiding v**:
- If t avoids v but shares edge with e, t MUST share base edge {a,b}
- If t avoids v but shares edge with f, t MUST share base edge {c,d}
- Covered by 2 base edges: {a,b}, {c,d}
- τ(avoiding) ≤ 2 ✓

**Total**: τ(T_pair) ≤ τ(containing) + τ(avoiding) ≤ 6

(Not 4 as originally hoped - the T_pair decomposition gives 6, not 4)
