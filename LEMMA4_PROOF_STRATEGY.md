# Lemma 4: fan_apex_exists - Detailed Proof Strategy

## Theorem Statement

```lean
theorem fan_apex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (hExt_nonempty : (externalsOf G M A).Nonempty) :
    ∃ x : V, x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T
```

---

## Proof Outline

### Phase 1: Extract Structure from A

**Goal**: Decompose A = {a, b, c} and identify its edges

```lean
-- A is a triangle in G.cliqueFinset 3
have hA_3 : A ∈ G.cliqueFinset 3 := hM.1.1 hA
have hA_card : A.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hA_3 |>.2

-- A has 3 edges: {a,b}, {b,c}, {c,a}
-- Extract specific vertices (Fintype indexing)
obtain ⟨a, b, c, hA_eq, hab, hbc, hca⟩ := card_3_vertices_exist hA_card

-- Each edge is in G
have hab_edge : G.Adj a b := by
  have : {a, b} ∈ A.sym2 := by ...
  exact SimpleGraph.mem_cliqueFinset_iff.mp hA_3 |>.1 this

have hbc_edge : G.Adj b c := by ... -- similar
have hca_edge : G.Adj c a := by ... -- similar
```

### Phase 2: Use slot182 to Show Pairwise Edge-Sharing

**Goal**: Prove any two distinct externals share an edge

```lean
-- Import slot182: two_externals_share_edge (PROVEN)
-- This is our foundation

have h_pairwise_share : ∀ T₁ T₂ ∈ externalsOf G M A, T₁ ≠ T₂ → sharesEdgeWith T₁ T₂ :=
  fun T₁ T₂ hT₁ hT₂ hne =>
    two_externals_share_edge G M hM hM4 A hA T₁ T₂ hT₁ hT₂ hne

-- Also get triangle cardinality
have h_externals_3 : ∀ T ∈ externalsOf G M A, T.card = 3 := fun T hT =>
  SimpleGraph.mem_cliqueFinset_iff.mp hT.1 |>.2
```

### Phase 3: Analyze Individual Externals

**Goal**: For each external, determine which edge of A it shares

```lean
-- Define helper: which_edge_of_A determines which A-edge an external uses
def which_edge_of_A (T A : Finset V) : Option (Finset V) :=
  if sharesEdgeWith T {a, b} then some {a, b}
  else if sharesEdgeWith T {b, c} then some {b, c}
  else if sharesEdgeWith T {c, a} then some {c, a}
  else none

-- For each external T, exactly one of these is true:
-- sharesEdgeWith T {a, b} OR
-- sharesEdgeWith T {b, c} OR
-- sharesEdgeWith T {c, a}
-- (By definition of external: shares with A, but which edge?)

have h_external_shares_one_edge : ∀ T ∈ externalsOf G M A,
    (sharesEdgeWith T {a, b}) ∨
    (sharesEdgeWith T {b, c}) ∨
    (sharesEdgeWith T {c, a}) := fun T hT =>
  -- T shares an edge with A by definition
  have : sharesEdgeWith T A := hT.2.2.1
  -- A's edges are {a,b}, {b,c}, {c,a}
  -- If T shares edge with A, must share with one of these
  extract_shared_edge_of_A T A this
```

### Phase 4: Case Analysis on Edge Distribution

**Goal**: Show that regardless of edge distribution, common vertex x exists

#### Case A: All Externals Use the Same A-Edge

```lean
-- Subcase: All externals use edge {a, b}
-- Then each external T = {a, b, x_T} for some x_T ∉ A

have h_all_use_ab : ∀ T ∈ externalsOf G M A, sharesEdgeWith T {a, b} := by
  -- (This is the assumption for this subcase)
  sorry

-- Key: {a, b, x₁} and {a, b, x₂} must share an edge
-- T₁ = {a, b, x₁}, T₂ = {a, b, x₂}
-- T₁ ∩ T₂ ⊇ {a, b}
-- So T₁ and T₂ share the edge {a, b}

have h_common_edge : ∀ T₁ T₂ ∈ externalsOf G M A, T₁ ≠ T₂ →
    sharesEdgeWith T₁ T₂ ∧ {a, b} ∈ (T₁.sym2 ∩ T₂.sym2) := by
  -- Two triangles sharing edge {a,b} each must be {a, b, x} for some x
  -- Their intersection is {a, b} ∪ (mutual third vertices)
  sorry

-- Now: if T₁ = {a, b, x₁} and T₂ = {a, b, x₂} and they share an edge,
-- the edge must involve {a, b} and possibly one of x₁, x₂
-- Case 1: edge is {a, b} → already satisfied
-- Case 2: edge is {a, x₁} → then x₁ ∈ T₂, so x₁ = x₂
-- Case 3: edge is {b, x₁} → then x₁ ∈ T₂, so x₁ = x₂

-- By induction/pigeonhole: x₁ = x₂ = x for all externals in this subcase
have h_same_x : ∃ x, x ∉ A ∧ ∀ T ∈ externalsOf G M A, T = {a, b, x} := by
  sorry  -- follows from case analysis above
```

#### Case B: Externals Use Different A-Edges

```lean
-- Subcase: Some externals use {a, b}, some use {b, c}, etc.
-- By pigeonhole, at least one x appears in multiple externals

-- More specifically: show x must appear in ALL externals

-- Consider T₁ using {a, b} → T₁ = {a, b, x₁}
-- Consider T₂ using {b, c} → T₂ = {b, c, x₂}
-- Consider T₃ using {c, a} → T₃ = {c, a, x₃}

-- They pairwise share edges (by slot182):
have hT₁T₂_share : sharesEdgeWith T₁ T₂ := h_pairwise_share T₁ T₂ (by simp) (by simp) (by simp)

-- T₁ ∩ T₂ ⊇ {b} (from edge-sharing analysis)
-- Both T₁ and T₂ contain at least one more vertex beyond {a,b,c}
-- Shared vertices: b is common to both A-edges
-- So T₁ ∩ T₂ ⊇ {b, ...}

-- If edge is {b, x₁}: x₁ ∈ T₂ → x₁ ∈ {b, c, x₂}
-- x₁ ≠ b (since {b, x₁} is edge with x₁ ≠ b)
-- x₁ ≠ c (since T₁ = {a, b, x₁} and x₁ ∉ {a, b, c})
-- So x₁ = x₂

-- Similarly, T₂ and T₃ share an edge → x₂ = x₃
-- By transitivity: x₁ = x₂ = x₃ = x

-- For more than 3 externals (if they use repeated edges), same argument applies

have h_all_contain_x : ∃ x, x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T := by
  use x
  constructor
  · -- x ∉ A (since T = {a,b,x} and x ≠ a, x ≠ b, x not in A)
    sorry
  · -- ∀ T, x ∈ T
    sorry
```

### Phase 5: Conclusion

```lean
-- Combine all cases
cases h_all_use_ab_or_different_edges
case all_same =>
  exact h_same_x
case different_edges =>
  exact h_all_contain_x
```

---

## Key Lemmas Required

### Lemma 1: shares_edge_implies_intersection_size

```lean
lemma shares_edge_implies_intersection_size (T₁ T₂ : Finset V)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_share : sharesEdgeWith T₁ T₂) :
    (T₁ ∩ T₂).card ≥ 2 := by
  -- Two vertices u, v with u ≠ v appear in both T₁ and T₂
  obtain ⟨u, v, huv, hu_T₁, hv_T₁, hu_T₂, hv_T₂⟩ := h_share
  have hu_inter : u ∈ T₁ ∩ T₂ := by simp [hu_T₁, hu_T₂]
  have hv_inter : v ∈ T₁ ∩ T₂ := by simp [hv_T₁, hv_T₂]
  exact Finset.card_pair ⟨u, v, huv, hu_inter, hv_inter⟩ -- or use one_lt_card
```

### Lemma 2: triangle_structure_case_analysis

```lean
lemma triangle_structure_case_analysis (T : Finset V) (hT : T.card = 3)
    (a b c x : V) (hT_contains : a ∈ T ∧ b ∈ T) :
    ∃ y, T = {a, b, y} ∨ T = {a, b, c} := by
  -- If T has 3 elements and contains a, b, then T = {a, b, c} or T = {a, b, y} for some y ∉ {a,b}
  sorry
```

### Lemma 3: edge_distribution_pigeonhole

```lean
lemma edge_distribution_pigeonhole (externals : Finset (Finset V)) (A : Finset V)
    (hA_3 : A.card = 3) (h_all_share : ∀ T ∈ externals, ∃ e ∈ A.sym2, sharesEdgeWith T {e}) :
    ∃ x, ∀ T ∈ externals, x ∈ T := by
  -- With 3 edges and pairwise edge-sharing, common vertex must exist
  sorry
```

---

## Proof Complexity Analysis

| Step | Complexity | Lines | Difficulty |
|------|-----------|-------|-----------|
| Phase 1: Extract A structure | Low | 30-40 | ⭐ |
| Phase 2: Use slot182 | Very Low | 10-20 | ⭐ |
| Phase 3: Analyze edges | Medium | 50-80 | ⭐⭐⭐ |
| Phase 4: Case analysis | High | 150-200 | ⭐⭐⭐⭐ |
| Phase 5: Conclusion | Low | 20-30 | ⭐ |
| **Total** | | **260-370** | **⭐⭐⭐⭐** |

---

## Testing Strategy

### Test Case 1: Triangle (K₃)

```
G = K₃: vertices {0, 1, 2}, all edges
M = {{0, 1, 2}} (single triangle)
A = {0, 1, 2}
Externals: empty (no other triangles possible)
Result: hExt_nonempty fails, theorem vacuously true ✓
```

### Test Case 2: Complete Graph (K₄)

```
G = K₄: vertices {0, 1, 2, 3}, complete
M = {{0, 1, 2}, {0, 1, 3}} or other valid packing

Case: A = {0, 1, 2}
Edges of A: {0,1}, {1,2}, {2,0}
Possible externals sharing {0,1}: {0, 1, 3}
Possible externals sharing {1,2}: {1, 2, 3}
Possible externals sharing {2,0}: {2, 0, 3}

All three contain x = 3 ✓
Fan apex exists: x = 3
```

### Test Case 3: Path (P₄)

```
G = path 0--1--2--3
M = {{0,1,2}} (single triangle, since no K₃ with 4 vertices in path)
Actually, P₄ has only 2 triangles: {0,1,2} and {1,2,3}
Try M = {{0,1,2}} (one element)
Externals of {0,1,2}: {1, 2, 3} shares edge {1,2}
Can we add {1,2,3} to M? Check if it's a packing with {0,1,2}
Intersection: {1,2} has card 2, violates packing ✗

Better: M = {{0,1,2}, {1,2,3}} is NOT a packing (intersection card 2)
M = {{0,1,2}} is maximum packing (no more disjoint triangles available)

So: Fan apex theorem is vacuous for this case (no other externals)
```

### Test Case 4: K₅ with Structured Packing

```
G = K₅: {0,1,2,3,4}
M = {{0,1,2}, {0,3,4}} (packing: intersection at most vertex 0)

A = {0,1,2}
Edges: {0,1}, {1,2}, {2,0}

Possible externals:
- {0,1,3}, {0,1,4}: both share {0,1}, both contain 3 or 4 → maybe same vertex?
- {1,2,3}, {1,2,4}: both share {1,2}, both contain 3 or 4
- {0,2,3}, {0,2,4}: both share {0,2}

For {0,1,3} and {1,2,3}:
- Share edge {1,3} (both contain 1 and 3)
- Both contain 3 → apex x = 3?

For {0,1,3} and {0,2,3}:
- Share edge {0,3}
- Both contain 3 → apex x = 3 ✓

For {1,2,3} and {0,2,3}:
- Share edge {2,3}
- Both contain 3 → apex x = 3 ✓

Conjecture: x = 3 (the vertex not in A adjacent to all of {0,1,2})
```

---

## Potential Pitfalls & Solutions

### Pitfall 1: Not all externals may use A-edges exclusively

**Problem**: Definition of external requires shares edge with A only. But what if we haven't checked it's maximal?

**Solution**: Use isMaxPacking condition. If T ∉ M and shares edge with A, then either:
- T ∉ G.cliqueFinset 3 (not a triangle) → contradicts hT.1
- T is covered by some m ∈ M (shares 2+ vertices)

Since we're looking at externals (T ∉ M), and the packing is maximal, our externals are exactly those sharing an edge with A.

### Pitfall 2: Multiple externals might use the same A-edge

**Problem**: How do we handle when all externals use {a,b}?

**Solution**: Covered by Case A above. All are {a, b, x} for some x, and any two must share an edge (by slot182). Only possibility is x₁ = x₂.

### Pitfall 3: Circular reasoning using slot182?

**Problem**: Isn't slot182 about pairwise edge-sharing across all externals? Aren't we using that to prove common vertex exists?

**Solution**: No circularity. Slot182 is proven independently from fan_apex. We use slot182 as a *lemma* to show pairwise edge-sharing, then apply case analysis to extract common vertex.

### Pitfall 4: What if no x exists outside A?

**Problem**: Could all externals be in A somehow?

**Solution**: No. By definition, externals are T ∉ M. Since A ∈ M, we have T ≠ A. If all externals were in A, we'd have |A| ≥ 4 (at least 4 distinct triangles). But |A| = 1 (it's a single element of M).

---

## Lean Tactics Reference

### Useful Tactics
- `obtain ⟨...⟩ := h_pairwise_share`: Extract edge-sharing witness
- `cases h_case_analysis`: Case split on which A-edge
- `simp [sharesEdgeWith, Finset.mem_inter]`: Simplify membership
- `Finset.card_pair`: Get cardinality 2 from two distinct elements
- `by_contra h_neg`: Proof by contradiction (alternative to cases)
- `omega`: Arithmetic reasoning on cardinalities

### Hypotheses from slot182

```lean
-- After using two_externals_share_edge:
have h_T₁_T₂_share : sharesEdgeWith T₁ T₂ := ...
obtain ⟨u, v, huv, hu_T₁, hv_T₁, hu_T₂, hv_T₂⟩ := h_T₁_T₂_share
```

---

## Submission Checklist

Before submitting to Aristotle:

- [ ] All scaffolding lemmas from slot182 are available
- [ ] Case analysis on 3 edges of A is complete (no missed cases)
- [ ] Verified that x ∉ A (explicit proof, not just intuition)
- [ ] Used slot182 correctly (not circular reasoning)
- [ ] No proof-by-type-escape patterns
- [ ] No self-loop witnesses (Sym2.mk(x,x))
- [ ] Tested on K₃, K₄, K₅ examples
- [ ] All sorries are in scaffolding lemmas only (main theorem complete)

---

## References

- **Slot182**: `two_externals_share_edge` - PROVEN
- **Pattern 6**: `external_share_common_vertex` - FALSE (different concept)
- **Pattern 16**: `helly_three_triangles` - FALSE (claims common EDGE, not vertex)
- **Fan Structure Insight**: FALSE_LEMMAS.md, Section "KEY INSIGHT"

---

**Status**: Ready for implementation
**Difficulty**: ⭐⭐⭐⭐ (4/5)
**Lines of Code**: ~270-370
**Estimated Proof Time**: 4-6 hours with Aristotle
