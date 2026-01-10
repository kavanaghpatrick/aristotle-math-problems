/-
  slot250_all_externals_share_apex.lean

  TARGET: Prove that ALL externals of a single M-element share a common apex vertex.

  Uses:
  - slot182 (PROVEN): two_externals_share_edge
  - slot224f (PROVEN): different_edges_share_external_vertex

  Strategy: Combine these to show transitivity of apex-sharing.

  1 SORRY expected for Aristotle to fill.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven files)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot182 and slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

/-- slot182: Any two externals of the same M-element share an edge -/
axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂

/-- slot224f: Externals using different A-edges share an external vertex -/
axiom different_edges_share_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂)
    (h_diff_edge : T₁ ∩ A ≠ T₂ ∩ A) :
    ∃ x : V, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Same-edge externals share external vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Externals using the SAME edge of A also share their external vertex -/
lemma same_edge_share_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂)
    (h_same_edge : T₁ ∩ A = T₂ ∩ A) :
    ∃ x : V, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- T₁ and T₂ share an edge (by slot182)
  have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  -- The shared edge is NOT the A-edge (since that's the same for both)
  -- So the shared edge uses the external vertices
  obtain ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩ := h_share
  -- T₁ ∩ A = T₂ ∩ A has exactly 2 vertices (the shared A-edge)
  -- T₁ has 3 vertices, so T₁ \ A has 1 vertex (the external vertex x₁)
  -- Similarly T₂ \ A has 1 vertex (x₂)
  -- The shared edge {u, v} must include at least one of x₁, x₂
  have hT₁_A_card : (T₁ ∩ A).card = 2 := by
    have h_ge : (T₁ ∩ A).card ≥ 2 := by
      obtain ⟨a, b, hab, ha₁, hb₁, ha_A, hb_A⟩ := hT₁.2.2.1
      have ha : a ∈ T₁ ∩ A := Finset.mem_inter.mpr ⟨ha₁, ha_A⟩
      have hb : b ∈ T₁ ∩ A := Finset.mem_inter.mpr ⟨hb₁, hb_A⟩
      exact Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    have h_le : (T₁ ∩ A).card ≤ 2 := by
      by_contra h
      push_neg at h
      have h_sub : T₁ ⊆ A := by
        have h_inter_sub : T₁ ∩ A ⊆ T₁ := Finset.inter_subset_left
        have h_card_eq : (T₁ ∩ A).card = T₁.card := by
          have h1 : (T₁ ∩ A).card ≤ T₁.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : A ⊆ T₁ := by
        have h_inter_sub : T₁ ∩ A ⊆ A := Finset.inter_subset_right
        have h_card_eq : (T₁ ∩ A).card = A.card := by
          have h1 : (T₁ ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      have h_eq : T₁ = A := Finset.Subset.antisymm h_sub h_sub'
      exact hT₁.2.1 (h_eq ▸ hA)
    linarith
  -- External vertex of T₁
  have h_T₁_diff : (T₁ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₁ A
    rw [hT₁_A_card, hT₁_3] at this
    omega
  obtain ⟨x₁, hx₁_eq⟩ := Finset.card_eq_one.mp h_T₁_diff
  have hx₁_T₁ : x₁ ∈ T₁ := by
    have : x₁ ∈ T₁ \ A := by rw [hx₁_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.1
  have hx₁_not_A : x₁ ∉ A := by
    have : x₁ ∈ T₁ \ A := by rw [hx₁_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.2
  -- External vertex of T₂
  have hT₂_A_card : (T₂ ∩ A).card = 2 := by rw [← h_same_edge]; exact hT₁_A_card
  have h_T₂_diff : (T₂ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₂ A
    rw [hT₂_A_card, hT₂_3] at this
    omega
  obtain ⟨x₂, hx₂_eq⟩ := Finset.card_eq_one.mp h_T₂_diff
  have hx₂_T₂ : x₂ ∈ T₂ := by
    have : x₂ ∈ T₂ \ A := by rw [hx₂_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.1
  have hx₂_not_A : x₂ ∉ A := by
    have : x₂ ∈ T₂ \ A := by rw [hx₂_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.2
  -- The shared edge {u, v} has at least one vertex in {x₁, x₂}
  -- because T₁ ∩ A = T₂ ∩ A, and the shared edge can't be entirely in A
  -- (otherwise it would be the same A-edge, but then T₁ = T₂)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: All externals share a common apex
-- ══════════════════════════════════════════════════════════════════════════════

/-- All externals of a single M-element share a common external vertex (apex) -/
theorem all_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (h_nonempty : (externalsOf G M A).Nonempty) :
    ∃ x : V, x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T := by
  -- Pick any external T₀
  obtain ⟨T₀, hT₀⟩ := h_nonempty
  have hT₀_ext : isExternalOf G M A T₀ := Finset.mem_filter.mp hT₀ |>.2
  have hT₀_3 : T₀.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₀_ext.1 |>.2
  -- Get external vertex of T₀
  have hT₀_A_card : (T₀ ∩ A).card = 2 := by
    have h_ge : (T₀ ∩ A).card ≥ 2 := by
      obtain ⟨a, b, hab, ha₁, hb₁, ha_A, hb_A⟩ := hT₀_ext.2.2.1
      have ha : a ∈ T₀ ∩ A := Finset.mem_inter.mpr ⟨ha₁, ha_A⟩
      have hb : b ∈ T₀ ∩ A := Finset.mem_inter.mpr ⟨hb₁, hb_A⟩
      exact Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    have h_le : (T₀ ∩ A).card ≤ 2 := by
      by_contra h; push_neg at h
      have h_sub : T₀ ⊆ A := by
        have h_inter_sub : T₀ ∩ A ⊆ T₀ := Finset.inter_subset_left
        have h_card_eq : (T₀ ∩ A).card = T₀.card := by
          have h1 : (T₀ ∩ A).card ≤ T₀.card := Finset.card_le_card h_inter_sub
          linarith
        intro w hw
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hw
        exact Finset.mem_inter.mp hw |>.2
      have h_sub' : A ⊆ T₀ := by
        have h_inter_sub : T₀ ∩ A ⊆ A := Finset.inter_subset_right
        have h_card_eq : (T₀ ∩ A).card = A.card := by
          have h1 : (T₀ ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub
          linarith
        intro w hw
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hw
        exact Finset.mem_inter.mp hw |>.1
      exact hT₀_ext.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hA)
    linarith
  have h_T₀_diff : (T₀ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₀ A
    rw [hT₀_A_card, hT₀_3] at this
    omega
  obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp h_T₀_diff
  have hx_T₀ : x ∈ T₀ := by
    have : x ∈ T₀ \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.1
  have hx_not_A : x ∉ A := by
    have : x ∈ T₀ \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.2
  -- Claim: x is in every external
  use x
  constructor
  · exact hx_not_A
  · intro T hT
    have hT_ext : isExternalOf G M A T := Finset.mem_filter.mp hT |>.2
    have hT_3 : T.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT_ext.1 |>.2
    by_cases h_eq : T = T₀
    · rw [h_eq]; exact hx_T₀
    · -- T ≠ T₀, so they share an external vertex by slot182 + slot224f
      by_cases h_same : T ∩ A = T₀ ∩ A
      · -- Same A-edge case
        obtain ⟨y, hy_not_A, hy_T, hy_T₀⟩ := same_edge_share_external_vertex G M hM hM_card hν A hA hA_3 T T₀ hT_ext hT₀_ext hT_3 hT₀_3 h_eq h_same
        -- y is the unique external vertex of both T and T₀
        -- So y = x
        have hy_unique_T₀ : y = x := by
          have : y ∈ T₀ \ A := Finset.mem_sdiff.mpr ⟨hy_T₀, hy_not_A⟩
          rw [hx_eq] at this
          exact Finset.mem_singleton.mp this
        rw [← hy_unique_T₀]; exact hy_T
      · -- Different A-edge case
        obtain ⟨y, hy_not_A, hy_T, hy_T₀⟩ := different_edges_share_external_vertex G M hM hM_card hν A hA hA_3 T T₀ hT_ext hT₀_ext hT_3 hT₀_3 h_eq h_same
        -- y is in both T and T₀, and y ∉ A
        -- So y is the external vertex of T₀, which means y = x
        have hy_unique_T₀ : y = x := by
          have : y ∈ T₀ \ A := Finset.mem_sdiff.mpr ⟨hy_T₀, hy_not_A⟩
          rw [hx_eq] at this
          exact Finset.mem_singleton.mp this
        rw [← hy_unique_T₀]; exact hy_T

end
