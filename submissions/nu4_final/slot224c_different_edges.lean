/-
  slot224c_different_edges.lean

  FOCUSED LEMMA: Externals using different edges of A share external vertex.

  PROVEN AXIOM (slot182): two_externals_share_edge
    Any two distinct externals of M-element A share an edge (intersection ≥ 2).

  THEOREM: different_edges_share_external_vertex
    If T₁, T₂ are externals of A using different edges of A, they share x ∉ A.

  PROOF:
    Let A = {a, b, c} be a triangle.
    T₁ uses edge {a, b}: T₁ = {a, b, x₁} where x₁ ∉ A.
    T₂ uses edge {b, c}: T₂ = {b, c, x₂} where x₂ ∉ A.
    (Edges {a,b} and {b,c} share vertex b.)

    By slot182: |T₁ ∩ T₂| ≥ 2.

    T₁ ∩ T₂ = {a, b, x₁} ∩ {b, c, x₂}
            = {b} ∪ ({a} ∩ {b, c, x₂}) ∪ ({x₁} ∩ {b, c, x₂})

    Since a ≠ b, a ≠ c (triangle), {a} ∩ {b, c} = ∅.
    And a ∉ A implies a ≠ x₂... wait, a ∈ A!

    Actually: {a} ∩ {b, c, x₂} = ∅ if a ∉ {b, c, x₂}.
    We have a ≠ b, a ≠ c (distinct vertices of triangle A).
    And x₂ ∉ A, so x₂ ≠ a.
    Therefore {a} ∩ {b, c, x₂} = ∅.

    Similarly: {x₁} ∩ {b, c, x₂}.
    x₁ ∉ A, so x₁ ≠ b, x₁ ≠ c.
    So {x₁} ∩ {b, c} = ∅.
    Thus {x₁} ∩ {b, c, x₂} = {x₁} ∩ {x₂} = {x₁} if x₁ = x₂, else ∅.

    So: T₁ ∩ T₂ = {b} ∪ (∅ if x₁ ≠ x₂ else {x₁})
               = {b} if x₁ ≠ x₂
               = {b, x₁} if x₁ = x₂

    For |T₁ ∩ T₂| ≥ 2: must have x₁ = x₂.

    Therefore: x = x₁ = x₂ is the common external vertex.

  1 SORRY for Aristotle.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (minimal)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ (t ∩ A).card ≥ 2 ∧
  ∀ B ∈ M, B ≠ A → (t ∩ B).card < 2

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: slot182
-- ══════════════════════════════════════════════════════════════════════════════

axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    (T₁ ∩ T₂).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External has exactly one vertex outside A
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_has_unique_outside_vertex (T A : Finset V)
    (hT_3 : T.card = 3) (hA_3 : A.card = 3) (hTA : (T ∩ A).card = 2) :
    ∃! x, x ∈ T ∧ x ∉ A := by
  -- T has 3 vertices, T ∩ A has 2, so exactly 1 is outside A
  have h_diff : (T \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T A
    omega
  rw [Finset.card_eq_one] at h_diff
  obtain ⟨x, hx_eq⟩ := h_diff
  use x
  constructor
  · constructor
    · have : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
      exact Finset.mem_sdiff.mp this |>.1
    · have : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
      exact Finset.mem_sdiff.mp this |>.2
  · intro y ⟨hy_T, hy_not_A⟩
    have : y ∈ T \ A := Finset.mem_sdiff.mpr ⟨hy_T, hy_not_A⟩
    rw [hx_eq] at this
    exact Finset.mem_singleton.mp this

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Externals using adjacent (different) edges of A share a common external vertex. -/
theorem different_edges_share_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂)
    -- They use different edges of A
    (h_diff_edge : T₁ ∩ A ≠ T₂ ∩ A) :
    ∃ x : V, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- Step 1: Get intersection bound from slot182
  have h_inter := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  -- |T₁ ∩ T₂| ≥ 2

  -- Step 2: Get unique external vertices
  have hT₁_A_card : (T₁ ∩ A).card = 2 := by
    have h := hT₁.2.2.1
    interval_cases n : (T₁ ∩ A).card <;> try omega
    · -- n = 3 would mean T₁ ⊆ A
      have : T₁ ⊆ A := by
        intro v hv
        by_contra hv_not_A
        have : v ∈ T₁ \ A := Finset.mem_sdiff.mpr ⟨hv, hv_not_A⟩
        have hcard : (T₁ \ A).card ≥ 1 := Finset.card_pos.mpr ⟨v, this⟩
        have hsum := Finset.card_sdiff_add_card_inter T₁ A
        rw [hT₁_3] at hsum
        omega
      have hT₁_sub_A : T₁ ⊆ A := this
      have hT₁_eq_A : T₁ = A := by
        apply Finset.eq_of_subset_of_card_le hT₁_sub_A
        rw [hT₁_3, hA_3]
      -- But T₁ is external, so T₁ ∉ M, but A ∈ M
      rw [hT₁_eq_A] at hT₁
      exact hT₁.2.1 hA

  have hT₂_A_card : (T₂ ∩ A).card = 2 := by
    have h := hT₂.2.2.1
    interval_cases n : (T₂ ∩ A).card <;> try omega
    · have : T₂ ⊆ A := by
        intro v hv
        by_contra hv_not_A
        have : v ∈ T₂ \ A := Finset.mem_sdiff.mpr ⟨hv, hv_not_A⟩
        have hcard : (T₂ \ A).card ≥ 1 := Finset.card_pos.mpr ⟨v, this⟩
        have hsum := Finset.card_sdiff_add_card_inter T₂ A
        rw [hT₂_3] at hsum
        omega
      have hT₂_eq_A : T₂ = A := by
        apply Finset.eq_of_subset_of_card_le this
        rw [hT₂_3, hA_3]
      rw [hT₂_eq_A] at hT₂
      exact hT₂.2.1 hA

  -- Step 3: Get unique external vertices x₁, x₂
  obtain ⟨x₁, ⟨hx₁_T₁, hx₁_not_A⟩, hx₁_unique⟩ :=
    external_has_unique_outside_vertex T₁ A hT₁_3 hA_3 hT₁_A_card
  obtain ⟨x₂, ⟨hx₂_T₂, hx₂_not_A⟩, hx₂_unique⟩ :=
    external_has_unique_outside_vertex T₂ A hT₂_3 hA_3 hT₂_A_card

  -- Step 4: T₁ ∩ A and T₂ ∩ A are different edges of A, sharing exactly 1 vertex
  have h_A_edges_share_one : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card = 1 := by
    -- Two distinct 2-subsets of a 3-set share exactly 1 element
    have h1 : (T₁ ∩ A).card = 2 := hT₁_A_card
    have h2 : (T₂ ∩ A).card = 2 := hT₂_A_card
    have h_sub1 : T₁ ∩ A ⊆ A := Finset.inter_subset_right
    have h_sub2 : T₂ ∩ A ⊆ A := Finset.inter_subset_right
    -- In a 3-element set, two 2-element subsets intersect in 1 element
    have h_union : (T₁ ∩ A) ∪ (T₂ ∩ A) ⊆ A := Finset.union_subset h_sub1 h_sub2
    have h_union_card : ((T₁ ∩ A) ∪ (T₂ ∩ A)).card ≤ 3 :=
      le_trans (Finset.card_le_card h_union) (le_of_eq hA_3)
    -- |X ∪ Y| = |X| + |Y| - |X ∩ Y|
    have h_inclusion := Finset.card_union_add_card_inter (T₁ ∩ A) (T₂ ∩ A)
    -- 2 + 2 - |inter| ≤ 3 → |inter| ≥ 1
    -- Also |inter| ≤ min(2, 2) = 2
    -- Since they're different (h_diff_edge), |inter| < 2, so |inter| = 1
    have h_inter_le : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card < 2 := by
      by_contra h_ge_2
      push_neg at h_ge_2
      -- If |inter| ≥ 2 and both sets have size 2, they're equal
      have h_eq : T₁ ∩ A = T₂ ∩ A := by
        apply Finset.eq_of_subset_of_card_le
        · intro v hv
          exact Finset.mem_of_mem_inter_left hv
        · calc (T₂ ∩ A).card = 2 := h2
            _ ≤ ((T₁ ∩ A) ∩ (T₂ ∩ A)).card := h_ge_2
            _ ≤ (T₁ ∩ A).card := Finset.card_inter_le_left _ _
      exact h_diff_edge h_eq
    omega

  -- Step 5: Compute |T₁ ∩ T₂| in terms of common A-vertices and external vertices
  -- T₁ = (T₁ ∩ A) ∪ {x₁}, T₂ = (T₂ ∩ A) ∪ {x₂}
  have hT₁_decomp : T₁ = (T₁ ∩ A) ∪ {x₁} := by
    ext v
    constructor
    · intro hv
      by_cases hv_A : v ∈ A
      · left; exact Finset.mem_inter.mpr ⟨hv, hv_A⟩
      · right; rw [Finset.mem_singleton]; exact hx₁_unique v ⟨hv, hv_A⟩
    · intro hv
      rcases Finset.mem_union.mp hv with hv_inter | hv_sing
      · exact Finset.mem_of_mem_inter_left hv_inter
      · rw [Finset.mem_singleton] at hv_sing; rw [hv_sing]; exact hx₁_T₁

  have hT₂_decomp : T₂ = (T₂ ∩ A) ∪ {x₂} := by
    ext v
    constructor
    · intro hv
      by_cases hv_A : v ∈ A
      · left; exact Finset.mem_inter.mpr ⟨hv, hv_A⟩
      · right; rw [Finset.mem_singleton]; exact hx₂_unique v ⟨hv, hv_A⟩
    · intro hv
      rcases Finset.mem_union.mp hv with hv_inter | hv_sing
      · exact Finset.mem_of_mem_inter_left hv_inter
      · rw [Finset.mem_singleton] at hv_sing; rw [hv_sing]; exact hx₂_T₂

  -- Step 6: |T₁ ∩ T₂| = |common A-vertices| + |{x₁} ∩ {x₂}|
  -- = 1 + (1 if x₁ = x₂ else 0)
  -- For |T₁ ∩ T₂| ≥ 2, need x₁ = x₂
  have h_inter_formula : (T₁ ∩ T₂).card = ((T₁ ∩ A) ∩ (T₂ ∩ A)).card + if x₁ = x₂ then 1 else 0 := by
    -- T₁ ∩ T₂ = ((T₁ ∩ A) ∪ {x₁}) ∩ ((T₂ ∩ A) ∪ {x₂})
    -- = ((T₁ ∩ A) ∩ (T₂ ∩ A)) ∪ ((T₁ ∩ A) ∩ {x₂}) ∪ ({x₁} ∩ (T₂ ∩ A)) ∪ ({x₁} ∩ {x₂})
    -- (T₁ ∩ A) ∩ {x₂} = ∅ since x₂ ∉ A
    -- {x₁} ∩ (T₂ ∩ A) = ∅ since x₁ ∉ A
    -- So T₁ ∩ T₂ = ((T₁ ∩ A) ∩ (T₂ ∩ A)) ∪ ({x₁} ∩ {x₂})
    sorry

  -- Step 7: Conclude x₁ = x₂
  rw [h_A_edges_share_one] at h_inter_formula
  have : (T₁ ∩ T₂).card ≥ 2 := h_inter
  have h_x_eq : x₁ = x₂ := by
    by_contra h_ne_x
    simp only [h_ne_x, ↓reduceIte, add_zero] at h_inter_formula
    omega

  -- Step 8: Return the common external vertex
  use x₁
  exact ⟨hx₁_not_A, hx₁_T₁, h_x_eq ▸ hx₂_T₂⟩

end
