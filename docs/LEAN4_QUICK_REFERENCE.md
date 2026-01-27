# Lean 4 Quick Reference: 6-Packing Proof Tactics

## Witness Extraction (Nonempty → ∃)

```lean
-- Pattern: Extract from Nonempty
obtain ⟨witness, hwit⟩ := h  -- h : Set.Nonempty P

-- Example: Extract external triangle
obtain ⟨T₁, hT₁⟩ := h1  -- h1 : (externalsWithEdge G a b c).Nonempty
```

## Membership Unpacking (mem_filter)

```lean
-- Unpack membership in filtered set
simp only [externalsWithEdge, Finset.mem_filter] at hT₁
-- Now hT₁ is expanded into components:
-- - hT₁ : T₁ ∈ (G.cliqueFinset 3).filter (fun T => T ≠ {a,b,c} ∧ ...)

-- Further decompose:
obtain ⟨hT₁_clique, hT₁_ne_E, hT₁_edge, hT₁_miss⟩ := hT₁
```

## Finset Intersection Bounds

```lean
-- Key inequality: If |T₁| = 3, |T₂| = 3, and they share specific edges,
-- their intersection is bounded

-- Method 1: by_contra + omega
have hinter : (T₁ ∩ T₂).card ≤ 1 := by
  by_contra h
  push_neg at h      -- h : (T₁ ∩ T₂).card > 1
  omega              -- Contradiction from cardinality arithmetic

-- Method 2: Case analysis on structure
have hinter : (T₁ ∩ T₂).card ≤ 1 := by
  simp only [Finset.card_eq_one]
  intro h_contra
  -- T₁ ∩ T₂ has 2+ elements, but structure prevents this
  omega
```

## Finset Construction and Membership

```lean
-- Define multi-element finset
set S : Finset (Finset V) := {T₁, T₂, T₃, B, C, D}

-- Check membership
have hT₁_in_S : T₁ ∈ S := by simp [S, Finset.mem_insert, Finset.mem_singleton]

-- General membership in insert:
simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
```

## Case Splitting on Finset Membership

```lean
-- Pattern: Split on all possible elements
intro t ht
simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
rcases ht with (rfl | rfl | rfl | rfl | rfl | rfl)
-- Now 6 separate goals, one for each element

-- Shorter with interval_cases:
interval_cases t
-- Auto-generates cases if t is proven finite and members enumerable
```

## Pairwise Property Proof

```lean
-- Prove Set.Pairwise condition
have h_pairwise : Set.Pairwise (S : Set (Finset V)) (fun t t' => (t ∩ t').card ≤ 1) := by
  simp only [Set.Pairwise]
  intro t ht t' ht' hne
  -- Now prove (t ∩ t').card ≤ 1 for arbitrary t ≠ t' in S

-- Or directly unfold in problem:
unfold isTrianglePacking at hS_packing
constructor
· intro t ht; exact hS_all_triangles t ht
· simp only [Set.Pairwise]; intro t ht t' ht' hne
  -- Case split and apply specific bounds
```

## Extracting Pairwise from Original Packing

```lean
-- Given hM : isTrianglePacking G M
-- Extract the pairwise property
have h_pair : Set.Pairwise (M : Set (Finset V)) (fun e f => (e ∩ f).card ≤ 1) := hM.2

-- Use it
have hBC : (B ∩ C).card ≤ 1 := by
  simp only [Set.Pairwise] at h_pair
  exact h_pair B hB C hC hBC_ne
```

## Distinctness Proofs (Using Contradiction)

```lean
-- Prove two triangles are distinct
have hT₁_ne_T₂ : T₁ ≠ T₂ := by
  intro h
  rw [h] at hT₁_property    -- Substitute T₂ for T₁
  exact contradiction       -- hT₁_property contradicts known fact about T₂
```

## Cardinality Calculation

```lean
-- Pattern for computing |{a, b, c, d, e, f}| where all distinct

have hcard : S.card = 6 := by
  simp only [S, Finset.card_insert_of_notMem]
  -- Establishes all distinctness hypotheses
  simp only [ha_ne_b, ha_ne_c, ..., he_ne_f]  -- All ≠ hypotheses
  simp only [Finset.card_singleton]
  norm_num

-- More direct: Use Finset.card_insert_of_notMem repeatedly
have : S.card = Finset.card {T₁, T₂, T₃, B, C, D} := rfl
simp [Finset.card_insert_of_notMem, hT₁_ne_T₂, hT₁_ne_T₃, ...] at this
norm_num at this
```

## Contradiction Tactics

```lean
-- omega: Automatically solves linear arithmetic contradictions
omega

-- push_neg: Simplify negations (useful in by_contra)
intro h
push_neg at h    -- Converts ¬(P ∧ Q) to ¬P ∨ ¬Q, etc.

-- linarith: Linear arithmetic reasoning
have : 6 ≤ 4 := by linarith
omega

-- simp_all: Simplify with all hypotheses
simp_all only []  -- Usually finds contradictions automatically
```

## Unfolding Definitions in Context

```lean
-- Unfold type1Exists
unfold type1Exists at h1
-- h1 : (externalsWithEdge G a b c).Nonempty

-- Combined unfold + simp
simp only [type1Exists, externalsWithEdge, Finset.mem_filter] at h1
-- h1 is now fully expanded into simpler terms

-- Unfold in proof goal
unfold isTrianglePacking
-- Changes goal from "isTrianglePacking G S" to definition's RHS
```

## Type Extraction Pattern (Complete)

```lean
-- Type 1: {a, b, x} where x ∉ {a,b,c}
obtain ⟨T₁, hT₁⟩ := h1
simp only [externalsWithEdge, Finset.mem_filter] at hT₁
obtain ⟨hT₁_clique, hT₁_ne, hT₁_ab, hT₁_c_not⟩ := hT₁

-- Type 2: {b, c, y} where y ∉ {a,b,c}
obtain ⟨T₂, hT₂⟩ := h2
simp only [externalsWithEdge, Finset.mem_filter] at hT₂
obtain ⟨hT₂_clique, hT₂_ne, hT₂_bc, hT₂_a_not⟩ := hT₂

-- Type 3: {c, a, z} where z ∉ {a,b,c}
obtain ⟨T₃, hT₃⟩ := h3
simp only [externalsWithEdge, Finset.mem_filter] at hT₃
obtain ⟨hT₃_clique, hT₃_ne, hT₃_ca, hT₃_b_not⟩ := hT₃
```

## Proof by Contradiction (Standard Pattern)

```lean
-- Goal: ¬(P ∧ Q ∧ R)
intro ⟨hP, hQ, hR⟩  -- Assume P, Q, R

-- Do derivation...

omega  -- Contradiction is now obvious
```

## Universal Quantification Over Finset

```lean
-- Prove property holds for all elements in finset
have h_all : ∀ t ∈ S, P t := by
  intro t ht
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with (rfl | rfl | ... | rfl)
  -- Case 1: t = T₁; prove P T₁
  · exact pT₁
  -- Case 2: t = T₂; prove P T₂
  · exact pT₂
  -- ... etc
```

---

## Critical Error Patterns to Avoid

| Error | Cause | Fix |
|-------|-------|-----|
| `simp` doesn't expand definitions | Need to unfold explicitly | Use `simp only [defn]` or `unfold defn` |
| Card equations fail | Not using distinctness hypotheses | Add `simp [h_ne]` before `norm_num` |
| `omega` times out | Non-linear or non-integer arithmetic | Use `linarith` or structure explicitly |
| Can't match on union | Need to simplify membership first | `simp only [Finset.mem_insert]` first |
| "Expected Sort, got Type" | Confusing Set vs Finset | Use `(S : Set (Finset V))` for Set.Pairwise |

---

## Exact Code Snippets for 6-Packing

### Extract All Three Witnesses (Compact)

```lean
obtain ⟨T₁, hT₁⟩ := h1; simp only [externalsWithEdge, Finset.mem_filter] at hT₁
obtain ⟨hT₁_clique, hT₁_ne_E, hT₁_ab, hT₁_c_not⟩ := hT₁

obtain ⟨T₂, hT₂⟩ := h2; simp only [externalsWithEdge, Finset.mem_filter] at hT₂
obtain ⟨hT₂_clique, hT₂_ne_E, hT₂_bc, hT₂_a_not⟩ := hT₂

obtain ⟨T₃, hT₃⟩ := h3; simp only [externalsWithEdge, Finset.mem_filter] at hT₃
obtain ⟨hT₃_clique, hT₃_ne_E, hT₃_ca, hT₃_b_not⟩ := hT₃
```

### Prove 15 Pairwise Bounds (Template)

```lean
have h_T₁T₂ : (T₁ ∩ T₂).card ≤ 1 := by
  by_contra h; push_neg at h
  -- T₁ = {a,b,x}, T₂ = {b,c,y}, T₁ ∩ T₂ ⊆ {b}, so card ≤ 1
  omega

have h_T₁T₃ : (T₁ ∩ T₃).card ≤ 1 := by omega
have h_T₂T₃ : (T₂ ∩ T₃).card ≤ 1 := by omega

-- For remaining 12 pairs, either omega directly or extract bound from original packing
have h_BC : (B ∩ C).card ≤ 1 := by
  have : Set.Pairwise (M : Set (Finset V)) (fun e f => (e ∩ f).card ≤ 1) := hM.2
  simp only [Set.Pairwise] at this
  exact this B hB C hC hBC
```

### Distinctness + Cardinality (Compact)

```lean
have h_distinct : T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₂ ≠ T₃ ∧ T₁ ≠ B ∧ T₁ ≠ C ∧ T₁ ≠ D ∧
                  T₂ ≠ B ∧ T₂ ≠ C ∧ T₂ ≠ D ∧ T₃ ≠ B ∧ T₃ ≠ C ∧ T₃ ≠ D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (intro h; rw [h] at *; omega)

have hS_card : S.card = 6 := by
  simp only [S, Finset.card_insert_of_notMem]
  simp only [h_distinct.1, h_distinct.2.1, h_distinct.2.2.1, h_distinct.2.2.2.1,
             h_distinct.2.2.2.2.1, h_distinct.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.1,
             h_distinct.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.1,
             h_distinct.2.2.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.2.2.1,
             h_distinct.2.2.2.2.2.2.2.2.2.2.2, hBC, hBD, hCD]
  norm_num
```

### Final Contradiction

```lean
have h_packing : isTrianglePacking G S := ⟨by simp [S]; intros; omega, by simp [Set.Pairwise]; intros; omega⟩
have h_too_big : S.card ≤ 4 := hNu4 S h_packing
rw [hS_card] at h_too_big
omega
```

