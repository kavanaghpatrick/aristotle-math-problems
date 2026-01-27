# Lean 4 Idioms & Patterns Used in Math Project

## Project-Specific Patterns

Based on analysis of `/Users/patrickkavanagh/math/proven/tuza/nu4/path4_scaffolding_complete.lean`

---

## 1. Heavy simp Usage Pattern

The project heavily relies on `simp +zetaDelta` and `simp +decide`:

```lean
-- Pattern 1: simp +zetaDelta
simp +zetaDelta at *
-- Expands all Finset operations and simplifies aggressively

-- Pattern 2: simp +decide
simp +decide [ Finset.subset_iff, Finset.mem_filter ]
-- Also use decide to resolve decidable propositions

-- Pattern 3: Combined
simp_all +decide [ Finset.ext_iff, Finset.subset_iff ]
-- simp_all applies simp to all hypotheses
```

**Why**: The project deals heavily with finite sets and decidable membership, so `simp +decide` automatically solves many finset operations.

---

## 2. aesop Pattern

```lean
-- aesop is used as a "try harder" simplifier
have h : P := by
  simp_all +decide
  exact absurd h_contradiction (by aesop)

-- aesop solves goals by:
-- 1. Breaking down logical connectives
-- 2. Trying standard library theorems
-- 3. Using simp lemmas
```

---

## 3. grind Pattern

```lean
-- grind is used for goals involving arithmetic or finsets after simplification
have h : a = b := by
  have h1 : a.card = b.card := by ...
  have h2 : a ⊆ b := by ...
  grind  -- Completes: a = b via card equality and subset

-- grind +ring for ring arithmetic
have h : x + y = y + x := by
  omega  -- or grind +ring
```

---

## 4. interval_cases Pattern

```lean
-- Used when the goal variable has bounded cardinality
have hcard : t.card ≤ 3 := ...

interval_cases _ : Finset.card t <;> simp_all +decide
-- Generates cases for cardinality = 0, 1, 2, 3
-- Each case then simplified by simp +decide

-- Pattern: Extract and case on small finite sets
have h_three : t.card = 3 := ...
rw [ Finset.card_eq_three ] at h_three
rcases h_three with ⟨ x, y, z, hx, hy, hz, hxyz ⟩
-- Now can reason about exact structure: t = {x, y, z}
```

---

## 5. Finset.eq_of_subset_of_card_le Pattern

```lean
-- Standard pattern for proving set equality when subsets and cards are known
have h1 : a ⊆ b := ...
have h2 : a.card = b.card := ...
have h3 : a = b := Finset.eq_of_subset_of_card_le h1 (by linarith)

-- Or in reverse:
have h1 : b ⊆ a := ...
have h2 : b.card = a.card := ...
have h3 : a = b := (Finset.eq_of_subset_of_card_le h1 (by linarith)).symm
```

---

## 6. by_contra + push_neg Pattern

```lean
-- Standard pattern for proving inequalities
have h : (t ∩ e).card ≥ 2 := by
  by_contra h_contra
  push_neg at h_contra  -- h_contra : (t ∩ e).card < 2

  -- Now have explicit contradiction
  have h1 : (t ∩ e).card ≤ 1 := by omega
  have h2 : (t ∩ e).card ≥ 2 := ... -- from earlier hypothesis
  omega
```

---

## 7. set vs let Pattern

The project uses both:

```lean
-- set: Creates a named definition that stays in context
set M' : Finset (Finset V) := (M \ {e}) ∪ {t1, t2}
have h : M'.card ≤ M.card := ...  -- Can use M' directly

-- let: Creates a local binding (less commonly used)
let S : Finset (Finset V) := {T₁, T₂, T₃, B, C, D}

-- In this project, prefer `set` for complex objects that will be reused
```

---

## 8. Finset.mem_filter + simp Pattern

```lean
-- Define a filter
def S_e := (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- Unpack membership
simp only [ S_e, Finset.mem_filter ] at h
-- Converts: h : t ∈ S_e  =>  h : t ∈ trianglesSharingEdge G e ∧ (∀ f ∈ M, ...)

-- Then further unpack
simp only [ trianglesSharingEdge, Finset.mem_filter ] at h
-- Converts: h : t ∈ (G.cliqueFinset 3).filter (fun x => ...) ∧ ...
```

---

## 9. Proof by Contradiction with Large Packing Pattern

```lean
-- Pattern used in larger_packing_of_disjoint_pair
theorem larger_packing_of_disjoint_pair ... : False := by
  set M' : Finset (Finset V) := (M \ {e}) ∪ {t1, t2}
  have hM'_packing : isTrianglePacking G M' := by
    simp +zetaDelta
    unfold S_e at *
    simp_all +decide [...]
  have hM'_card : M'.card ≤ M.card := by ...
  have h_not_in_M : t1 ∉ M \ {e} ∧ t2 ∉ M \ {e} := by ...
  grind +ring  -- Derives contradiction from card inequalities
```

---

## 10. Set.Pairwise Usage

```lean
-- Packing definition uses Set.Pairwise
def isTrianglePacking G M :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- To extract for two specific elements:
have h_pair : Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := hM.2
simp only [Set.Pairwise] at h_pair
-- h_pair : ∀ x, x ∈ (M : Set V) → ∀ y, y ∈ (M : Set V) → x ≠ y → ...

-- Apply to specific elements
exact h_pair B hB C hC hBC
```

---

## 11. Finset.card_eq_three / Finset.card_eq_two Pattern

```lean
-- Extract components from small finsets
have h : t.card = 3 := ...
rw [Finset.card_eq_three] at h
obtain ⟨ x, y, z, hx, hy, hz, hxyz ⟩ := h
-- Now: x ∈ t, y ∈ t, z ∈ t, x ≠ y, y ≠ z, x ≠ z, t = {x, y, z}

-- Or for edges:
have h : e.card = 2 := ...
rw [Finset.card_eq_two] at h
obtain ⟨ u, v, huv, huve ⟩ := h
-- Now: u ∈ e, v ∈ e, u ≠ v, e = {u, v}
```

---

## 12. have + obtain Combined Pattern

```lean
-- Pattern 1: Nested have + obtain
have h_card : (t ∩ e).card ≥ 2 := by ...
obtain ⟨ u, v, ⟨ hu, hv ⟩ ⟩ : ∃ u v, u ∈ t ∩ e ∧ v ∈ t ∩ e := by
  have := Finset.one_lt_card.mp h_card
  exact Exists.imp fun u => by aesop

-- Pattern 2: Direct obtain from hypothesis
obtain ⟨ u, hu ⟩ := Finset.exists_mem_ne hcard v
-- Extracts u ∈ s with u ≠ v from Finset.exists_mem_ne
```

---

## 13. Finset.union_subset / Finset.inter_subset Patterns

```lean
-- Proving union subset
have h : A ∪ B ⊆ C := by
  exact Finset.union_subset hA hB
  -- Need: A ⊆ C and B ⊆ C

-- Proving things about intersection
have h : x ∈ A ∩ B := by
  simp [Finset.mem_inter]
  exact ⟨ hxA, hxB ⟩

have h : (A ∩ B) ⊆ C := by
  exact Finset.inter_subset_left.trans hC
```

---

## 14. rw [Finset.ext_iff] for Equality

```lean
-- Prove finset equality via extensionality
have h : A = B := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, ...]
  exact ⟨ fun hA => ..., fun hB => ... ⟩

-- Or directly:
rw [Finset.ext_iff]
intro x
simp only [Finset.mem_insert, ...]
exact ⟨ ..., ... ⟩
```

---

## 15. rotate_left / rotate_right for Goal Rearrangement

```lean
-- Used when goal order matters
theorem something ... : P ∧ Q ∧ R := by
  constructor
  · -- Prove P
  · constructor
    · -- Prove Q
    · rotate_left 1  -- Moves first goal to end temporarily
      -- Prove R
      -- Then rotate_left 1 restores order

-- Or use refine':
refine' ⟨ hP, hQ, hR ⟩
```

---

## 16. Finset.card_union_le and Finset.card_union_of_disjoint

```lean
-- For disjoint finsets
have h_disj : Disjoint A B := by ...
have h : (A ∪ B).card = A.card + B.card := by
  exact Finset.card_union_of_disjoint h_disj

-- For general union (upper bound)
have h : (A ∪ B).card ≤ A.card + B.card :=
  Finset.card_union_le A B
```

---

## 17. simp_all for Aggressive Simplification

```lean
-- Applies simp to all hypotheses and goal
simp_all +decide [...]

-- Equivalent to:
simp [...] at h1; simp [...] at h2; ...; simp [...]
-- But more concise

-- Common in larger proofs to clean up context
have h1 : P := ...; have h2 : Q := ...; simp_all only [h1, h2]
```

---

## 18. Finset.card_insert_of_notMem for Cardinality

```lean
-- Calculate card of {a, b, c, ...}
have ha_ne_b : a ≠ b := ...
have : ({a, b} : Finset V).card = 2 := by
  simp [Finset.card_insert_of_notMem, ha_ne_b]

-- Patterns:
-- - simp [Finset.card_insert_of_notMem, all_distinctness_hyps]
-- - Then norm_num to compute final number
```

---

## 19. cases h : Finset.max for Option Handling

```lean
-- Handling optional maximum
have := Finset.le_max h
cases h : Finset.max (...) <;> aesop
-- Pattern: case split on whether max exists
-- - Some m: Maximum exists
-- - None: Finset is empty
```

---

## 20. Finset.disjoint_left Pattern

```lean
-- Prove disjointness via element-wise reasoning
have h_disj : Disjoint A B := by
  exact Finset.disjoint_left.mpr fun x hx_A hx_B => ...
  -- Need to derive False from x ∈ A ∧ x ∈ B

-- Or verify that no element is in both:
simp_all +decide [Finset.disjoint_left]
```

---

## Summary Table

| Pattern | Use Case | Key Tactic |
|---------|----------|-----------|
| `simp +decide` | Finset simplification | `simp only [Finset.*, ...] at h` |
| `aesop` | Goal breakdown | Use after simplification |
| `grind` | Equality from inequalities | `grind +ring` for arithmetic |
| `interval_cases` | Bounded cardinality | Works with `Finset.card` |
| `by_contra + push_neg` | Prove negative | First push negation |
| `set ... :=` | Define reusable terms | Stays in context |
| `have + obtain` | Extract components | Chain for complex types |
| `rw [Finset.ext_iff]` | Finset equality | Then `intro x; simp` |
| `simp_all +decide` | Aggressive simp | Use to clean context |
| `omega` | Numeric contradiction | For final contradiction |

