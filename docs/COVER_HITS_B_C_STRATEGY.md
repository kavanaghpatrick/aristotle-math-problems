# Strategy for Proving cover_hits_sharing_B and cover_hits_sharing_C

## Problem Statement

In slot263_path4_explicit_aristotle.lean, lines 318-333, we have two sorries:

```lean
lemma cover_hits_sharing_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ cfg.B).card ≥ 2) (ht_not_A : (t ∩ cfg.A).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry

lemma cover_hits_sharing_C (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_C : (t ∩ cfg.C).card ≥ 2) (ht_not_D : (t ∩ cfg.D).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry
```

These lemmas must prove that **any triangle sharing ≥2 vertices with B (but ≤1 with A) is covered by the spine edge {v₁, v₂}**.

---

## Key Observations

### What We Know About t

1. **t is a triangle**: `t ∈ G.cliqueFinset 3`, so t has exactly 3 vertices forming a complete subgraph
2. **t shares ≥2 with B**: `(t ∩ cfg.B).card ≥ 2`
3. **t shares ≤1 with A**: `(t ∩ cfg.A).card ≤ 1`
4. **Path4 structure**:
   - `cfg.B = {v₁, v₂, b₃}`
   - `cfg.A ∩ cfg.B = {v₁}`
   - `cfg.B ∩ cfg.C = {v₂}`

### What We Know About the Cover

The path4_cover includes:
- All edges of A: `cfg.A.sym2` (covers triangles fully intersecting A)
- Spine edge {v₁, v₂}: covers triangles containing this edge
- Spine edge {v₂, v₃}: not relevant for B
- All edges of D: `cfg.D.sym2`

---

## Case Analysis Strategy

### Case 1: t ∈ M (t equals one of {A, B, C, D})

**Subcase 1a: t = A**
- If `t ∩ cfg.B ≥ 2`, but we also have `t ∩ cfg.A ≤ 1`, this is impossible (A intersects itself in 3)
- **Resolved by contradiction**

**Subcase 1b: t = B**
- All 3 edges of B are in the cover
- Any edge {x, y} where x, y ∈ B ∩ t = B is in the cover
- **Proven by inclusion**

**Subcase 1c: t = C**
- Shares exactly {v₂} with B (by PATH_4 structure)
- But we need `(t ∩ cfg.B).card ≥ 2`, contradiction
- **Resolved by contradiction**

**Subcase 1d: t = D**
- Shares ∅ or {v₂} with B at most... wait, let me reconsider the structure
- D = {v₃, d₂, d₃}, B = {v₁, v₂, b₃}
- These are completely disjoint (B ∩ D = ∅)
- If `(t ∩ cfg.B).card ≥ 2`, this is impossible for t = D
- **Resolved by contradiction**

### Case 2: t ∉ M (t is not a packing element)

By maximality of M, there exists m ∈ M such that `(t ∩ m).card ≥ 2`.

We're already told `(t ∩ cfg.B).card ≥ 2` and `(t ∩ cfg.A).card ≤ 1`.

**Subcase 2a: m = B**
- We have `(t ∩ cfg.B).card ≥ 2` and t ≠ B
- Since B = {v₁, v₂, b₃} and t is a triangle with 3 vertices:
  - t has ≥2 vertices from {v₁, v₂, b₃}
  - Since t ≠ B, t has at most 2 vertices from B
  - Therefore: t has exactly 2 vertices from B and 1 fresh vertex w

**Key insight**: t shares exactly 2 vertices with B. Which 2?

**Subcase 2a-i: t shares {v₁, v₂} with B**
- t = {v₁, v₂, w} for some w ∉ B
- The edge {v₁, v₂} = spine edge is in the cover
- **Covered by spine edge**

**Subcase 2a-ii: t shares {v₁, b₃} with B**
- t = {v₁, b₃, w} for some w ∉ B
- But t shares ≤1 with A = {v₁, a₂, a₃}
- If t = {v₁, b₃, w} and shares ≤1 with A:
  - v₁ ∈ A ∩ t (at least 1)
  - b₃ ∉ A, w ∉ A (since w ∉ B and A ∩ B = {v₁})
  - So this is consistent
- Now, t is a triangle, so it's a 3-clique
- Edges of t: {v₁, b₃}, {v₁, w}, {b₃, w}
- For maximality: (t ∩ B) ≥ 2 is satisfied ✓
- Which edge is covered by the 8-edge cover?
  - **{v₁, b₃} is part of B**, which is fully included in the cover ✓
- **Covered by B's edges**

**Subcase 2a-iii: t shares {v₂, b₃} with B**
- t = {v₂, b₃, w} for some w ∉ B
- Similar analysis: t is a triangle with these 3 vertices
- {v₂, b₃} is part of B's edges
- **Covered by B's edges**

### Summary of Cases for cover_hits_sharing_B

| Case | t structure | Sharing with B | Covering edge(s) | Reason |
|------|------------|---|---|---|
| t = B | {v₁, v₂, b₃} | {v₁, v₂, b₃} | All 3 edges of B | Included in cover |
| t = A | {v₁, a₂, a₃} | {v₁} | Impossible (share ≥2) | Contradiction |
| t = C | {v₂, v₃, c₃} | {v₂} | Impossible (share ≥2) | Contradiction |
| t = D | {v₃, d₂, d₃} | ∅ | Impossible (share ≥2) | Contradiction |
| t ∉ M, shares {v₁, v₂} | {v₁, v₂, w} | {v₁, v₂} | {v₁, v₂} spine | By definition |
| t ∉ M, shares {v₁, b₃} | {v₁, b₃, w} | {v₁, b₃} | {v₁, b₃} from B | B ⊂ cover |
| t ∉ M, shares {v₂, b₃} | {v₂, b₃, w} | {v₂, b₃} | {v₂, b₃} from B | B ⊂ cover |

---

## Lean Implementation for cover_hits_sharing_B

```lean
lemma cover_hits_sharing_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ cfg.B).card ≥ 2) (ht_not_A : (t ∩ cfg.A).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  -- Extract 2 distinct vertices from t ∩ cfg.B
  obtain ⟨x, y, hx_B, hy_B, hx_t, hy_t, hxy⟩ : ∃ x y : V,
    x ∈ cfg.B ∧ y ∈ cfg.B ∧ x ∈ t ∧ y ∈ t ∧ x ≠ y := by
    simpa using Finset.one_lt_card.1 ht_shares_B

  -- t is a 3-clique, so it has exactly 3 vertices. Let's denote the third as z.
  have ht_card : t.card = 3 := ht.2

  -- Since t is a clique and contains x, y, it also contains some z such that z ∈ t \ {x, y}
  have ⟨z, hz_t, hz_ne_x, hz_ne_y⟩ : ∃ z ∈ t, z ≠ x ∧ z ≠ y := by
    have : (t \ {x, y}).card ≥ 1 := by
      rw [card_sdiff]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 this
    use z
    exact ⟨Finset.mem_sdiff.1 hz |>.1, Finset.mem_sdiff.1 hz |>.2.1, Finset.mem_sdiff.1 hz |>.2.2⟩

  -- Case 1: t = cfg.B
  by_cases h_eq : t = cfg.B
  · rw [h_eq]
    -- All edges of B are in the cover
    have hxy_edge : s(x, y) ∈ cfg.B.sym2 := by
      simp [Finset.mem_sym2, hx_B, hy_B, hxy]
    use s(x, y)
    constructor
    · unfold path4_cover
      simp only [Finset.mem_union, Finset.mem_filter]
      left
      exact ⟨hxy_edge, ?_⟩ -- Need to show {x,y} ⊆ cfg.B edges
    · simp [Finset.mem_sym2, hx_t, hy_t]

  · -- Case 2: t ≠ cfg.B, so t is not in M (since (t ∩ cfg.B) ≥ 2 forces t ∈ M if t shares edges)
    -- By maximality and (t ∩ cfg.B).card ≥ 2, some edge of {x,y} is in B ⊆ cover

    -- The key insight: Since B = {v₁, v₂, b₃} and {x, y} ⊆ B with |{x,y}| = 2,
    -- we have one of three cases:
    -- (a) {x, y} = {v₁, v₂} → spine edge covers
    -- (b) {x, y} = {v₁, b₃} or {v₂, b₃} → covered by B's edges

    -- All three cases are covered by B's edges being in path4_cover
    have hB_in_cover : ∀ e ∈ cfg.B.sym2, (fun e => e ∈ G.edgeFinset) e →
        s(x, y) ∈ path4_cover G cfg := by
      intro e he_B_sym he_G
      unfold path4_cover
      simp only [Finset.mem_union, Finset.mem_filter]
      left
      exact ⟨he_B_sym, he_G⟩

    have hxy_B_sym : s(x, y) ∈ cfg.B.sym2 := by
      simp [Finset.mem_sym2, hx_B, hy_B, hxy]

    use s(x, y)
    constructor
    · -- Show edge is in cover
      -- The edge {x, y} ⊂ B (both in B), so it's in B.sym2
      -- If it's also a graph edge (which it must be, since t is a clique), it's in the cover
      unfold path4_cover
      simp only [Finset.mem_union, Finset.mem_filter]
      left
      constructor
      · exact hxy_B_sym
      · -- Need: G.Adj x y (since t is a clique containing x, y)
        exact ht.1 hx_t hy_t hxy
    · -- Show edge is in t
      simp [Finset.mem_sym2, hx_t, hy_t]
```

### For cover_hits_sharing_C: Symmetrical Argument

The proof for C is identical, but:
- B is replaced by C
- Spine edge {v₁, v₂} is replaced by {v₂, v₃}
- "shares ≤1 with A" is replaced by "shares ≤1 with D"

---

## Key Tactics Used

1. **`simpa using Finset.one_lt_card.1`** - Extract 2 distinct elements from a set with card ≥ 2
2. **`card_sdiff`** - Compute cardinality of set difference
3. **`simp [Finset.mem_sym2, ...]`** - Simplify set membership and edge membership
4. **Case analysis on `t = cfg.B`** - Either t is B (covered by all its edges) or t ≠ B (covered by the 2 shared vertices' edge)
5. **Use clique property** - Since t ∈ G.cliqueFinset 3, any two vertices in t are adjacent

---

## Estimated Proof Length

- **cover_hits_sharing_B**: ~40-50 lines (case analysis + membership simplification)
- **cover_hits_sharing_C**: ~40-50 lines (symmetric)

**Total**: ~100 lines of code to fill the two sorries in slot263.

---

## Why This Approach Works

The key insight is that **the spine edges {v₁, v₂} and {v₂, v₃} are "bridges" in the structure**:
- Any triangle sharing 2 or more vertices with B must contain at least one of {v₁, v₂}
- If it contains both, the edge {v₁, v₂} is in the triangle and in the cover
- If it contains only one, it still shares an edge with B (which is in the cover)

This is why 8 edges suffice:
- 3 from A (endpoints, covers A and A-externals)
- 1 from B-spine {v₁, v₂} (covers B and B-externals)
- 1 from C-spine {v₂, v₃} (covers C and C-externals)
- 3 from D (endpoints, covers D and D-externals)

Total: 8 edges cover all triangles in a maximal packing.
