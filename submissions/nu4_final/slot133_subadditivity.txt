/-
slot133: Subadditivity for Triangle Covering Number

GOAL: Prove τ(S₁ ∪ S₂) ≤ τ(S₁) + τ(S₂)

This is a fundamental lemma needed for combining local bounds into global bounds.

PROOF:
If E₁ covers S₁ and E₂ covers S₂, then E₁ ∪ E₂ covers S₁ ∪ S₂.
So τ(S₁ ∪ S₂) ≤ |E₁ ∪ E₂| ≤ |E₁| + |E₂|.
Taking infimum over valid covers gives τ(S₁ ∪ S₂) ≤ τ(S₁) + τ(S₂).
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A cover of triangle set S: edges that hit every triangle in S -/
def isCoverOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset (Sym2 V)) (S : Finset (Finset V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2

/-- Triangle covering number for a subset of triangles -/
noncomputable def triangleCoveringOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : ℕ :=
  if h : ∃ E : Finset (Sym2 V), isCoverOf G E S then
    (Finset.univ.filter (fun n : ℕ => ∃ E : Finset (Sym2 V), E.card = n ∧ isCoverOf G E S)).min'
      (by
        obtain ⟨E, hE⟩ := h
        use E.card
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨E, rfl, hE⟩)
  else 0

/-- Alternative direct definition using sInf -/
noncomputable def triangleCoveringOn' (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E.card = n ∧ isCoverOf G E S }

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Empty set has cover number 0 -/
lemma triangleCoveringOn_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringOn G ∅ = 0 := by
  unfold triangleCoveringOn
  simp only [dif_pos]
  · -- The set of covering sizes includes 0 (empty cover works)
    have h_min : (Finset.univ.filter (fun n : ℕ =>
        ∃ E : Finset (Sym2 V), E.card = n ∧ isCoverOf G E ∅)).min' _ = 0 := by
      apply le_antisymm
      · apply Finset.min'_le
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        use ∅
        simp only [Finset.card_empty, isCoverOf, Finset.empty_subset, Finset.not_mem_empty,
                   false_implies, implies_true, and_self]
      · exact Nat.zero_le _
    exact h_min
  · use ∅
    simp [isCoverOf]

/-- Singleton cover bound -/
lemma triangleCoveringOn_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    triangleCoveringOn G {t} ≤ 1 := by
  unfold triangleCoveringOn
  by_cases h : ∃ E : Finset (Sym2 V), isCoverOf G E {t}
  · simp only [dif_pos h]
    apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- t is a clique, so it has edges. Pick one.
    have h_tri := SimpleGraph.mem_cliqueFinset_iff.mp ht
    have h_card := h_tri.2
    have h_nonempty : t.Nonempty := by
      rw [Finset.card_eq_three] at h_card
      obtain ⟨a, b, c, -, h_eq⟩ := h_card
      exact ⟨a, by simp [h_eq]⟩
    -- Get two distinct vertices from t
    obtain ⟨a, ha⟩ := h_nonempty
    have h_exists_b : ∃ b ∈ t, b ≠ a := by
      by_contra h_all_eq
      push_neg at h_all_eq
      have : t = {a} := by
        ext x
        constructor
        · intro hx; simp [h_all_eq x hx]
        · intro hx; simp at hx; exact hx ▸ ha
      rw [this] at h_card
      simp at h_card
    obtain ⟨b, hb, hab⟩ := h_exists_b
    -- s(a,b) is an edge in t.sym2 and in G.edgeFinset
    use {s(a, b)}
    simp only [Finset.card_singleton]
    constructor
    · rfl
    · constructor
      · -- {s(a,b)} ⊆ G.edgeFinset
        intro e he
        simp only [Finset.mem_singleton] at he
        rw [he]
        exact SimpleGraph.mem_edgeFinset.mpr (h_tri.1 ha hb hab)
      · -- covers {t}
        intro t' ht'
        simp only [Finset.mem_singleton] at ht'
        rw [ht']
        use s(a, b)
        simp only [Finset.mem_singleton, Finset.mem_sym2_iff, true_and]
        exact ⟨a, b, hab, ha, hb, rfl⟩
  · simp only [dif_neg h]
    exact Nat.zero_le 1

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Subadditivity
-- ══════════════════════════════════════════════════════════════════════════════

/-- Union of covers is a cover of the union -/
lemma cover_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (E₁ E₂ : Finset (Sym2 V)) (S₁ S₂ : Finset (Finset V))
    (h₁ : isCoverOf G E₁ S₁) (h₂ : isCoverOf G E₂ S₂) :
    isCoverOf G (E₁ ∪ E₂) (S₁ ∪ S₂) := by
  constructor
  · -- (E₁ ∪ E₂) ⊆ G.edgeFinset
    intro e he
    simp only [Finset.mem_union] at he
    cases he with
    | inl h => exact h₁.1 h
    | inr h => exact h₂.1 h
  · -- Every triangle in S₁ ∪ S₂ is covered
    intro t ht
    simp only [Finset.mem_union] at ht
    cases ht with
    | inl h =>
      obtain ⟨e, he, het⟩ := h₁.2 t h
      exact ⟨e, Finset.mem_union_left _ he, het⟩
    | inr h =>
      obtain ⟨e, he, het⟩ := h₂.2 t h
      exact ⟨e, Finset.mem_union_right _ he, het⟩

/-- Subadditivity: τ(S₁ ∪ S₂) ≤ τ(S₁) + τ(S₂) -/
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) :
    triangleCoveringOn G (S₁ ∪ S₂) ≤ triangleCoveringOn G S₁ + triangleCoveringOn G S₂ := by
  unfold triangleCoveringOn

  -- Handle empty cases
  by_cases h₁_empty : S₁ = ∅
  · simp [h₁_empty]
    by_cases h₂_empty : S₂ = ∅
    · simp [h₂_empty]
    · by_cases h : ∃ E, isCoverOf G E S₂
      · simp only [dif_pos h]
        by_cases h' : ∃ E, isCoverOf G E ∅
        · simp only [dif_pos h']
          -- min' of sizes for empty set is 0
          have h_zero : (Finset.univ.filter (fun n : ℕ =>
              ∃ E : Finset (Sym2 V), E.card = n ∧ isCoverOf G E ∅)).min' _ = 0 := by
            apply le_antisymm
            · apply Finset.min'_le
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              use ∅; simp [isCoverOf]
            · exact Nat.zero_le _
          simp [h_zero]
        · simp only [dif_neg h']
      · simp only [dif_neg h]

  by_cases h₂_empty : S₂ = ∅
  · simp [h₂_empty]
    by_cases h : ∃ E, isCoverOf G E S₁
    · simp only [dif_pos h]
      by_cases h' : ∃ E, isCoverOf G E ∅
      · simp only [dif_pos h']
        have h_zero : (Finset.univ.filter (fun n : ℕ =>
            ∃ E : Finset (Sym2 V), E.card = n ∧ isCoverOf G E ∅)).min' _ = 0 := by
          apply le_antisymm
          · apply Finset.min'_le
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            use ∅; simp [isCoverOf]
          · exact Nat.zero_le _
        simp [h_zero]
      · simp only [dif_neg h']
    · simp only [dif_neg h]

  -- Main case: both non-empty
  by_cases h₁ : ∃ E, isCoverOf G E S₁
  · by_cases h₂ : ∃ E, isCoverOf G E S₂
    · -- Both have covers
      simp only [dif_pos h₁, dif_pos h₂]

      -- Get the optimal covers
      set n₁ := (Finset.univ.filter (fun n : ℕ =>
          ∃ E : Finset (Sym2 V), E.card = n ∧ isCoverOf G E S₁)).min' _ with hn₁
      set n₂ := (Finset.univ.filter (fun n : ℕ =>
          ∃ E : Finset (Sym2 V), E.card = n ∧ isCoverOf G E S₂)).min' _ with hn₂

      -- There exist covers achieving these sizes
      have hE₁ : ∃ E : Finset (Sym2 V), E.card = n₁ ∧ isCoverOf G E S₁ := by
        have := Finset.min'_mem _ _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      have hE₂ : ∃ E : Finset (Sym2 V), E.card = n₂ ∧ isCoverOf G E S₂ := by
        have := Finset.min'_mem _ _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this

      obtain ⟨E₁, hE₁_card, hE₁_cover⟩ := hE₁
      obtain ⟨E₂, hE₂_card, hE₂_cover⟩ := hE₂

      -- E₁ ∪ E₂ covers S₁ ∪ S₂
      have h_union_cover := cover_union G E₁ E₂ S₁ S₂ hE₁_cover hE₂_cover

      -- So ∃ cover for union
      have h_union : ∃ E, isCoverOf G E (S₁ ∪ S₂) := ⟨E₁ ∪ E₂, h_union_cover⟩
      simp only [dif_pos h_union]

      -- The min' for union is ≤ |E₁ ∪ E₂|
      apply Finset.min'_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      use E₁ ∪ E₂
      constructor
      · calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := Finset.card_union_le E₁ E₂
          _ = n₁ + n₂ := by rw [hE₁_card, hE₂_card]
      · sorry -- Need to show this equals n₁ + n₂, not just ≤

    · -- S₂ has no cover
      simp only [dif_neg h₂, add_zero]
      by_cases h_union : ∃ E, isCoverOf G E (S₁ ∪ S₂)
      · simp only [dif_pos h_union, dif_pos h₁]
        sorry -- Complex case
      · simp only [dif_neg h_union]

  · -- S₁ has no cover
    simp only [dif_neg h₁, zero_add]
    by_cases h₂ : ∃ E, isCoverOf G E S₂
    · by_cases h_union : ∃ E, isCoverOf G E (S₁ ∪ S₂)
      · simp only [dif_pos h_union, dif_pos h₂]
        sorry
      · simp only [dif_neg h_union]
    · simp only [dif_neg h₂]
      by_cases h_union : ∃ E, isCoverOf G E (S₁ ∪ S₂)
      · simp only [dif_pos h_union]
        sorry
      · simp only [dif_neg h_union]

/-- Simpler version using Nat.sInf directly -/
theorem tau_union_le_sum' (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) :
    triangleCoveringOn' G (S₁ ∪ S₂) ≤ triangleCoveringOn' G S₁ + triangleCoveringOn' G S₂ := by
  unfold triangleCoveringOn'
  -- If sInf {sizes for S₁} = τ₁ and sInf {sizes for S₂} = τ₂
  -- Then there exist covers E₁, E₂ with sizes arbitrarily close to τ₁, τ₂
  -- E₁ ∪ E₂ covers S₁ ∪ S₂ with size ≤ |E₁| + |E₂|
  -- So sInf {sizes for S₁ ∪ S₂} ≤ |E₁| + |E₂| ≤ τ₁ + τ₂ + ε
  -- Taking ε → 0 gives the result

  -- For Nat.sInf, we use that it equals the minimum element if the set is nonempty
  -- and 0 otherwise

  by_cases h₁ : { n | ∃ E, E.card = n ∧ isCoverOf G E S₁ }.Nonempty
  · by_cases h₂ : { n | ∃ E, E.card = n ∧ isCoverOf G E S₂ }.Nonempty
    · -- Both have covers
      obtain ⟨n₁, E₁, hE₁_card, hE₁_cov⟩ := h₁
      obtain ⟨n₂, E₂, hE₂_card, hE₂_cov⟩ := h₂

      have h_union := cover_union G E₁ E₂ S₁ S₂ hE₁_cov hE₂_cov
      have h_union_nonempty : { n | ∃ E, E.card = n ∧ isCoverOf G E (S₁ ∪ S₂) }.Nonempty := by
        use (E₁ ∪ E₂).card, E₁ ∪ E₂

      -- sInf ≤ element in set
      apply Nat.sInf_le
      use (E₁ ∪ E₂).card
      constructor
      · use E₁ ∪ E₂
      · calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := Finset.card_union_le E₁ E₂
          _ = n₁ + n₂ := by rw [hE₁_card, hE₂_card]
          _ ≤ sInf { n | ∃ E, E.card = n ∧ isCoverOf G E S₁ } +
              sInf { n | ∃ E, E.card = n ∧ isCoverOf G E S₂ } := by
            apply Nat.add_le_add
            · apply Nat.sInf_le
              use n₁; use E₁
            · apply Nat.sInf_le
              use n₂; use E₂
    · -- S₂ has no cover, so sInf = 0
      simp only [Set.not_nonempty_iff_eq_empty] at h₂
      simp only [h₂, Nat.sInf_empty, add_zero]
      -- S₁ ∪ S₂ might not have cover either
      sorry
  · -- S₁ has no cover
    simp only [Set.not_nonempty_iff_eq_empty] at h₁
    simp only [h₁, Nat.sInf_empty, zero_add]
    sorry

end
