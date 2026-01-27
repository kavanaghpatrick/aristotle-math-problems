# External Type Disjointness Analysis: PATH_4 τ ≤ 8 Proof

## Context: The Critical Gap

Aristotle proved in slot407 that **at most 2 external types exist per M-element**. This negates:
```
¬(∃ T₁, T₂, T₃ with types 1,2,3 all present with distinct fresh w₁, w₂, w₃)
```

However, slot263 needs to prove the REVERSE: If all 3 types DO exist, we can construct a valid packing with 6 triangles that contradicts ν=4.

## External Type Definitions

For M-element **A = {v₁, a₂, a₃}**, the three external types are:

| Type | Definition | Shares Edge | Formula |
|------|-----------|-------------|---------|
| **1** | T₁ = {v₁, a₂, w₁} | {v₁, a₂} ⊂ A | T₁ ∩ A = {v₁, a₂} |
| **2** | T₂ = {v₁, a₃, w₂} | {v₁, a₃} ⊂ A | T₂ ∩ A = {v₁, a₃} |
| **3** | T₃ = {a₂, a₃, w₃} | {a₂, a₃} ⊂ A | T₃ ∩ A = {a₂, a₃} |

**Key constraint**: Each w_i must be "fresh" (not in {v₁, v₂, v₃, a₂, a₃, b₃, c₃, d₂, d₃}).

---

## Question 1: Exact Conditions for Edge-Disjointness

### Pairwise External Intersections

The external types have **inherent** pairwise intersections:

1. **T₁ ∩ T₂ = {v₁}** (card = 1)
   - Both contain v₁; differ in second vertex (a₂ vs a₃)
   - w₁ ≠ w₂ ensures they're distinct

2. **T₁ ∩ T₃ = {a₂}** (card = 1)
   - T₁ = {v₁, a₂, w₁}; T₃ = {a₂, a₃, w₃}
   - Share only a₂ (v₁ ∉ T₃, w₁ ∉ A)

3. **T₂ ∩ T₃ = {a₃}** (card = 1)
   - T₂ = {v₁, a₃, w₂}; T₃ = {a₂, a₃, w₃}
   - Share only a₃ (v₁ ∉ T₃, w₂ ∉ A)

**These come from the DEFINITIONS, not from freshness constraints!**

### Externals vs M-elements (B, C, D)

For **A-externals vs B = {v₁, v₂, b₃}**:

| External | A ∩ B | Reasoning |
|----------|-------|-----------|
| T₁ = {v₁, a₂, w₁} | {v₁} | v₁ ∈ B; a₂ ∉ B; w₁ ∉ B (fresh) |
| T₂ = {v₁, a₃, w₂} | {v₁} | v₁ ∈ B; a₃ ∉ B; w₂ ∉ B (fresh) |
| T₃ = {a₂, a₃, w₃} | ∅ | None of {a₂, a₃, w₃} ∈ B |

**Freshness here means: w₃ ∉ {v₁, v₂, b₃}**, and since w₃ is fresh, this is guaranteed.

For **A-externals vs C = {v₂, v₃, c₃}**:
- T₁, T₂, T₃ all have card ≤ 1 intersection (all w_i avoid C)

For **A-externals vs D = {v₃, d₂, d₃}**:
- T₁, T₂, T₃ all have card ≤ 1 intersection (all w_i avoid D)

---

## Question 2: Freshness Requirements

**Answer: YES, all three w_i must be "fresh" (outside the 9-vertex core).**

### Why Freshness Matters

The constraint is:
```
w₁, w₂, w₃ ∉ {v₁, v₂, v₃, a₂, a₃, b₃, c₃, d₂, d₃}
```

**What freshness provides:**
1. **Prevents t_i = t_j for i ≠ j**: If w₁ = a₂, then T₁ = {v₁, a₂, a₂} (invalid - not a 3-clique)
2. **Isolates externals from B, C, D**: The formula T = {x, y, w_i} with w_i fresh guarantees (T ∩ B).card ≤ 1
3. **Ensures the 9-element PATH_4 structure is independent**: The packing {A, B, C, D} has a rigid intersection pattern; fresh w_i prevents interference

**Without freshness:**
- w₁ could equal a₃, making T₁ = {v₁, a₂, a₃} = ... but wait, that's almost A!
- If w₁ = a₃, then T₁ ∩ A = {v₁, a₂, a₃} = 3 vertices, violating the pairwise packing property

---

## Question 3: T₁, T₂, T₃ Pairwise Edge-Disjointness

**These are NOT edge-disjoint; they're vertex-packable (card ≤ 1 intersection).**

The proof uses the **packing property**, not edge-disjointness:

### Edge-Disjointness vs Packing Property

| Property | Definition | Why Edge-Disjoint Isn't Needed |
|----------|-----------|---------|
| **Edge-disjoint** | (t_i ∩ t_j) card = 0 | TOO STRONG; would prevent T₁, T₂ sharing v₁ |
| **Packing property** | (t_i ∩ t_j).card ≤ 1 | CORRECT; allows shared vertices but no shared edges |

**Edge-disjointness comes from a DIFFERENT property:**

Two triangles with card ≤ 1 intersection are **NOT necessarily edge-disjoint**.
- T₁ = {v₁, a₂, w₁}, T₂ = {v₁, a₃, w₂}, share vertex v₁
- If G.Adj v₁ a₂ AND G.Adj v₁ a₃ AND G.Adj a₂ a₃, then:
  - Edge {v₁, a₂} in T₁ is NOT in T₂ ✓ (edge-disjoint part)
  - Edge {v₁, a₃} in T₂ is NOT in T₁ ✓
  - Shared vertex v₁ can belong to edges in BOTH: {v₁, a₂} from T₁ and {v₁, a₃} from T₂

**For the contradiction proof (six_triangles_contradict_nu4):**
- We need the **packing property** (card ≤ 1 intersection)
- The proof counts the 6 triangles as a packing with card = 6 > 4, contradiction

---

## Question 4: The 15 Pairwise Intersections (Cleanest Proof)

### All 15 Pairs in {T₁, T₂, T₃, B, C, D}

| Pair | Bound | Justification |
|------|-------|---------------|
| (T₁, T₂) | ≤ 1 | Definition: {v₁} |
| (T₁, T₃) | ≤ 1 | Definition: {a₂} |
| (T₁, B) | ≤ 1 | Freshness + adjacency structure |
| (T₁, C) | ≤ 1 | Freshness: w₁ ∉ C vertices |
| (T₁, D) | ≤ 1 | Freshness: w₁ ∉ D vertices |
| (T₂, T₃) | ≤ 1 | Definition: {a₃} |
| (T₂, B) | ≤ 1 | Freshness + adjacency structure |
| (T₂, C) | ≤ 1 | Freshness: w₂ ∉ C vertices |
| (T₂, D) | ≤ 1 | Freshness: w₂ ∉ D vertices |
| (T₃, B) | ≤ 1 | Freshness: w₃ ∉ B, {a₂, a₃} ∉ B |
| (T₃, C) | ≤ 1 | Freshness: w₃ ∉ C, {a₂, a₃} ∉ C |
| (T₃, D) | ≤ 1 | Freshness: w₃ ∉ D, {a₂, a₃} ∉ D |
| (B, C) | ≤ 1 | PATH_4 structure: only {v₂} |
| (B, D) | ≤ 1 | PATH_4 structure: empty |
| (C, D) | ≤ 1 | PATH_4 structure: only {v₃} |

### Cleanest Proof Strategy

**Step-by-step for most pairs:**

```lean
-- Pair (T₁, T₂): Definitional
lemma inter_T1_T2 : (T₁ ∩ T₂).card ≤ 1 := by
  simp [T₁, T₂]
  -- Reduces to: ({v₁, a₂, w₁} ∩ {v₁, a₃, w₂}).card ≤ 1
  -- = {v₁}.card = 1

-- Pair (T₁, B): Requires freshness of w₁ and adjacency structure
lemma inter_T1_B : (T₁ ∩ B).card ≤ 1 := by
  -- T₁ = {v₁, a₂, w₁}, B = {v₁, v₂, b₃}
  -- Intersection: v₁ ∈ both (card ≥ 1)
  -- a₂ ∉ B (by PATH_4 structure: A ∩ B = {v₁})
  -- w₁ ∉ B (by freshness of w₁)
  -- Therefore: T₁ ∩ B = {v₁}, card = 1
  simp [T₁, B, hpath.1]  -- Unfold definitions and use PATH_4 structure
  exact by aesop

-- Pair (T₃, B): More subtle (no shared vertices directly)
lemma inter_T3_B : (T₃ ∩ B).card ≤ 1 := by
  -- T₃ = {a₂, a₃, w₃}, B = {v₁, v₂, b₃}
  -- No vertex in common (a₂, a₃, w₃ all avoid B by structure/freshness)
  -- Therefore: T₃ ∩ B = ∅, card = 0
  simp [T₃, B, hpath.1]
```

### The KEY INSIGHT

**For externals (T₁, T₂, T₃) vs M-elements (B, C, D):**

The freshness condition + PATH_4 structure automatically ensures:
- External fresh vertices avoid all M-element vertices
- External A-vertices {v₁, a₂, a₃} only appear in A, not B/C/D

**This is provable by card_le_one_of_subset_singleton once you unfold definitions.**

---

## Implementation in slot263

### Current Gap

Lines 318-333 have `sorry` on:
```lean
lemma cover_hits_sharing_B : ... := by sorry
lemma cover_hits_sharing_C : ... := by sorry
```

These need to cover triangles that share ≥2 vertices with B or C (but not A or D respectively).

### Solution Strategy

**Replace with case analysis on external types:**

```lean
-- For a triangle sharing B (not A), it must be an external type related to A
-- If t ∩ B has 2+ vertices and t ∩ A ≤ 1, then either:
-- 1. t = B (covered by full B edges)
-- 2. t is maximally adjacent to B, so ∃ edge {v1, v2} covers t (the spine edge)

lemma cover_hits_sharing_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ cfg.B).card ≥ 2)
    (ht_not_A : (t ∩ cfg.A).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  -- Case 1: t = B directly
  by_cases h_eq : t = cfg.B
  · rw [h_eq]
    -- t is in M, so its edges are in path4_cover
    use s(cfg.v1, cfg.v2)  -- spine edge from B
    simp [path4_cover]
    aesop
  · -- Case 2: t is maximal to B but not equal to B
    -- By maximality and ht_shares_B, there's an edge {x,y} ⊂ t ∩ B
    -- This edge must be covered; spine edge {v1, v2} ⊆ B covers it
    have ⟨x, y, hxy⟩ : ∃ x y : V, x ∈ t ∩ cfg.B ∧ y ∈ t ∩ cfg.B ∧ x ≠ y := by
      simpa using Finset.one_lt_card.1 ht_shares_B
    use s(cfg.v1, cfg.v2)
    constructor
    · unfold path4_cover; simp; left; simp; decide
    · -- Prove {v1, v2} ⊂ t
      have : x ∈ cfg.B ∧ y ∈ cfg.B := ⟨hxy.1.2, hxy.2.1.2⟩
      -- B = {v1, v2, b₃}, so x,y ∈ {v1, v2, b₃}
      -- If ht_shares_B ≥ 2 and we're in a triangle, x,y must both be in B
      -- And at least one of {v1, v2} must be in t
      aesop
```

---

## Mathematical Guarantee

**Lemma (Edge-Disjoint Packing to Vertex Packing):**

If {T₁, T₂, T₃, B, C, D} is a vertex packing (all pairs card ≤ 1 intersection) with |S| = 6, and each element is a triangle, then S contradicts ν = 4.

**Proof:** Packing = independent set in "conflict graph" where vertices are triangles and edges connect overlapping ones. A 6-vertex independent set in the conflict graph is impossible when ν = 4.

---

## Summary: The 4 Questions Answered

| Q | Answer | Why |
|---|--------|-----|
| **1. Exact edge-disjointness conditions?** | Comes from DEFINITIONS (T₁∩T₂={v₁}, etc.) + FRESHNESS (w_i avoid B/C/D) | Pair-specific; unfold definitions |
| **2. Fresh needed?** | YES, all 3 w_i must be outside {v₁,...,d₃} | Prevents T = {x,y,x} invalid, isolates from M-elements |
| **3. Prove T₁,T₂,T₃ pairwise ≤1?** | Definitional (packing property, not edge-disjoint) | {v₁}, {a₂}, {a₃} are the only intersections |
| **4. Cleanest 15-pair proof?** | Unfold definitions + use PATH_4 structure + freshness constraints | `simp [T₁, T₂, B, C, D]; aesop` handles most |

---

## Implementation Roadmap

1. **In slot263 (or new submission):** Replace `cover_hits_sharing_B/C` sorries
2. **Strategy:** Case on whether t ∈ M (if so, covered by endpoints); else covered by spine edge {v1,v2} or {v2,v3}
3. **Helper lemmas:** Pre-prove the 15 card ≤ 1 bounds as separate lemmas; use them in main proof
4. **Leverage:** The existing `six_triangles_contradict_nu4` proof shows the contrapositive; reverse it to "if 3 types exist, 6 triangles form a packing"

**Estimated effort:** 30-60 lines of Lean code using tactics: `simp`, `omega`, `aesop`, and explicit case analysis on 3-vertex sets.
