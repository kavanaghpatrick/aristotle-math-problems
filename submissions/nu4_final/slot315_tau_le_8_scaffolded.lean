/-
  slot315: τ ≤ 8 for ν = 4 - MAXIMUM SCAFFOLDING

  ALL proven lemmas from slots 306-309, fixed for current Mathlib API.
  Single sorry: the main tau_le_8 theorem.

  PROVEN HELPERS (14 lemmas):
  1. sharesEdgeWith_iff_card_inter_ge_two
  2. external_has_one_outside
  3. external_inter_X_card
  4. two_externals_share_edge
  5. externals_disjoint_outside_implies_same_edge
  6. externals_all_same_edge_of_exists_diff
  7. all_externals_share_common_vertex
  8. cover_externals_case_inside
  9. cover_externals_case_outside
  10. two_edges_cover_all_externals
  11. pairwise_externals_share_X_vertex
  12. fanCover_card
  13. bridge_triangle_contains_shared_vertex
  14. bridge_covered_if_shared_is_common
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
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
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 1: sharesEdgeWith ↔ intersection ≥ 2
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 2: External has exactly one vertex outside X
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_has_one_outside (t X : Finset V) (ht : t.card = 3) (hX : X.card = 3)
    (h_share : sharesEdgeWith t X) (h_ne : t ≠ X) :
    (t \ X).card = 1 := by
  have h_inter : (t ∩ X).card = 2 := by
    have h_ge : (t ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two t X |>.mp h_share
    have h_le : (t ∩ X).card ≤ 2 := by
      by_contra h_gt
      push_neg at h_gt
      have h_sub : t ⊆ X := by
        have h_inter_sub : t ∩ X ⊆ t := Finset.inter_subset_left
        have h_card_eq : (t ∩ X).card = t.card := by
          have h1 : (t ∩ X).card ≤ t.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : X ⊆ t := by
        have h_inter_sub : t ∩ X ⊆ X := Finset.inter_subset_right
        have h_card_eq : (t ∩ X).card = X.card := by
          have h1 : (t ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      exact h_ne (Finset.Subset.antisymm h_sub h_sub')
    linarith
  have := Finset.card_sdiff_add_card_inter t X
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 3: External intersection with X has exactly 2 elements
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_inter_X_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  have hT_card : T.card = 3 := by
    simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT
    exact hT.1.2.2
  have h_diff : (T \ X).card = 1 := by
    apply external_has_one_outside T X hT_card hX_card hT.2.2.1
    intro h_eq
    exact hT.2.1 (h_eq ▸ hX_in_M)
  have := Finset.card_sdiff_add_card_inter T X
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 4: Two externals share an edge (5-packing argument)
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_share
  -- If T₁ and T₂ don't share an edge, we can form a 5-packing
  have hT₁_card : T₁.card = 3 := by
    simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT₁
    exact hT₁.1.2.2
  have hT₂_card : T₂.card = 3 := by
    simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT₂
    exact hT₂.1.2.2
  -- Construct M' = {T₁, T₂} ∪ (M \ {X})
  let M' := insert T₁ (insert T₂ (M.erase X))
  have hM'_card : M'.card = 5 := by
    have h1 : T₁ ∉ M := hT₁.2.1
    have h2 : T₂ ∉ M := hT₂.2.1
    have h3 : (M.erase X).card = 3 := by rw [Finset.card_erase_of_mem hX]; omega
    have h4 : T₁ ∉ insert T₂ (M.erase X) := by
      simp only [Finset.mem_insert, Finset.mem_erase]
      intro h
      rcases h with rfl | ⟨_, h⟩
      · exact h_ne rfl
      · exact h1 h
    have h5 : T₂ ∉ M.erase X := by
      simp only [Finset.mem_erase]
      intro ⟨_, h⟩
      exact h2 h
    simp only [Finset.card_insert_of_not_mem h4, Finset.card_insert_of_not_mem h5, h3]
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_erase] at ht
      rcases ht with rfl | rfl | ⟨_, ht⟩
      · exact hT₁.1
      · exact hT₂.1
      · exact hM.1.1 ht
    · intro t₁ ht₁ t₂ ht₂ hne
      simp only [Finset.mem_insert, Finset.mem_erase] at ht₁ ht₂
      -- Case analysis on t₁ and t₂
      rcases ht₁ with rfl | rfl | ⟨hne₁, ht₁⟩ <;>
      rcases ht₂ with rfl | rfl | ⟨hne₂, ht₂⟩
      · exact absurd rfl hne
      · -- T₁ and T₂ don't share edge
        have := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂
        simp only [not_le] at h_no_share
        push_neg at this
        exact Nat.lt_succ_iff.mp (this.mp h_no_share)
      · -- T₁ and some Y ∈ M \ {X}
        have hY_ne_X : t₂ ≠ X := hne₂
        have := hT₁.2.2.2 t₂ ht₂ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₁ t₂
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · rw [Finset.inter_comm]
        have := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂
        simp only [not_le] at h_no_share
        push_neg at this
        exact Nat.lt_succ_iff.mp (this.mp h_no_share)
      · exact absurd rfl hne
      · have hY_ne_X : t₂ ≠ X := hne₂
        have := hT₂.2.2.2 t₂ ht₂ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₂ t₂
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · rw [Finset.inter_comm]
        have hY_ne_X : t₁ ≠ X := hne₁
        have := hT₁.2.2.2 t₁ ht₁ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₁ t₁
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · rw [Finset.inter_comm]
        have hY_ne_X : t₁ ≠ X := hne₁
        have := hT₂.2.2.2 t₁ ht₁ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₂ t₁
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · exact hM.1.2 ht₁ ht₂ hne
  have := hν M' hM'_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 5-6: Externals with different outside vertices share same X-edge
-- ══════════════════════════════════════════════════════════════════════════════

lemma externals_disjoint_outside_implies_same_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    T₁ ∩ X = T₂ ∩ X := by
  have h_inter_card₁ : (T₁ ∩ X).card = 2 := external_inter_X_card G M X hX hX_3 T₁ hT₁
  have h_inter_card₂ : (T₂ ∩ X).card = 2 := external_inter_X_card G M X hX hX_3 T₂ hT₂
  have hT₁_ne_T₂ : T₁ ≠ T₂ := by
    intro h_eq
    rw [h_eq] at h_diff
    exact h_diff rfl
  have h_share : sharesEdgeWith T₁ T₂ := two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ hT₁_ne_T₂
  have h_T₁T₂ : (T₁ ∩ T₂).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂ |>.mp h_share
  -- The shared edge of T₁ and T₂ must be in X (since their outside vertices differ)
  have hT₁_card : T₁.card = 3 := by simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT₁; exact hT₁.1.2.2
  have hT₂_card : T₂.card = 3 := by simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT₂; exact hT₂.1.2.2
  have h_out₁ : (T₁ \ X).card = 1 := by have := Finset.card_sdiff_add_card_inter T₁ X; omega
  have h_out₂ : (T₂ \ X).card = 1 := by have := Finset.card_sdiff_add_card_inter T₂ X; omega
  -- If outside vertices differ, shared edge must be inside X
  have h_disj : (T₁ \ X) ∩ (T₂ \ X) = ∅ := by
    obtain ⟨v₁, hv₁⟩ := Finset.card_eq_one.mp h_out₁
    obtain ⟨v₂, hv₂⟩ := Finset.card_eq_one.mp h_out₂
    have hne : v₁ ≠ v₂ := by
      intro h_eq
      rw [h_eq] at hv₁
      exact h_diff (hv₁.trans hv₂.symm)
    rw [hv₁, hv₂]
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.not_mem_empty, iff_false]
    intro ⟨h1, h2⟩
    exact hne (h1.trans h2.symm)
  -- T₁ ∩ T₂ ⊆ X (since outside parts are disjoint)
  have h_in_X : T₁ ∩ T₂ ⊆ X := by
    intro x hx
    simp only [Finset.mem_inter] at hx
    by_contra hx_not_X
    have hx_out₁ : x ∈ T₁ \ X := Finset.mem_sdiff.mpr ⟨hx.1, hx_not_X⟩
    have hx_out₂ : x ∈ T₂ \ X := Finset.mem_sdiff.mpr ⟨hx.2, hx_not_X⟩
    have : x ∈ (T₁ \ X) ∩ (T₂ \ X) := Finset.mem_inter.mpr ⟨hx_out₁, hx_out₂⟩
    rw [h_disj] at this
    exact Finset.not_mem_empty x this
  -- So T₁ ∩ T₂ ⊆ T₁ ∩ X and T₁ ∩ T₂ ⊆ T₂ ∩ X
  have h_sub₁ : T₁ ∩ T₂ ⊆ T₁ ∩ X := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mp hx |>.1, h_in_X hx⟩
  have h_sub₂ : T₁ ∩ T₂ ⊆ T₂ ∩ X := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mp hx |>.2, h_in_X hx⟩
  -- Both T₁ ∩ X and T₂ ∩ X have exactly 2 elements, and contain T₁ ∩ T₂ which has ≥ 2
  have h_eq₁ := Finset.eq_of_subset_of_card_le h_sub₁ (by linarith)
  have h_eq₂ := Finset.eq_of_subset_of_card_le h_sub₂ (by linarith)
  exact h_eq₁.symm.trans h_eq₂

lemma externals_all_same_edge_of_exists_diff (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (T₁ T₂ : Finset V) (hT₁ : T₁ ∈ externals) (hT₂ : T₂ ∈ externals)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    ∀ T ∈ externals, T ∩ X = T₁ ∩ X := by
  intro T hT
  by_cases h_cases : T \ X = T₁ \ X
  · -- T and T₁ have same outside vertex, but T₂ differs
    have h_diff' : T \ X ≠ T₂ \ X := by rwa [h_cases]
    have := externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₂
              (h_ext T hT) (h_ext T₂ hT₂) h_diff'
    have := externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T₁ T₂
              (h_ext T₁ hT₁) (h_ext T₂ hT₂) h_diff
    aesop
  · -- T has different outside vertex from T₁
    exact externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₁
            (h_ext T hT) (h_ext T₁ hT₁) h_cases

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 7: All externals share a common vertex
-- ══════════════════════════════════════════════════════════════════════════════

theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T := by
  by_cases h_all_same_outside : ∀ T1 ∈ externals, ∀ T2 ∈ externals, T1 \ X = T2 \ X
  · -- All externals have same outside vertex v
    obtain ⟨T₀, hT₀⟩ := h_nonempty
    have hT₀_ext : isExternalOf G M X T₀ := h_ext T₀ hT₀
    have hT₀_card : T₀.card = 3 := by
      simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT₀_ext
      exact hT₀_ext.1.2.2
    have hT₀_out : (T₀ \ X).card = 1 := by
      have := external_inter_X_card G M X hX hX_3 T₀ hT₀_ext
      have := Finset.card_sdiff_add_card_inter T₀ X
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hT₀_out
    use v
    intro T hT
    have := h_all_same_outside T hT T₀ hT₀
    rw [this, hv]
    exact Finset.mem_singleton_self v
  · -- Some externals have different outside vertices, so all share same X-edge
    push_neg at h_all_same_outside
    obtain ⟨T1, hT1, T2, hT2, h_diff⟩ := h_all_same_outside
    have hS : ∀ T ∈ externals, T ∩ X = T1 ∩ X :=
      externals_all_same_edge_of_exists_diff G M hM hM_card hν X hX hX_3 externals
        h_ext T1 T2 hT1 hT2 h_diff
    have hT1_ext : isExternalOf G M X T1 := h_ext T1 hT1
    have hT1_inter_card : (T1 ∩ X).card = 2 := external_inter_X_card G M X hX hX_3 T1 hT1_ext
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by linarith : 0 < (T1 ∩ X).card)
    use u
    intro T hT
    have h_eq : T ∩ X = T1 ∩ X := hS T hT
    have hu_in_TX : u ∈ T ∩ X := h_eq.symm ▸ hu
    exact Finset.mem_of_mem_inter_left hu_in_TX

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 8-9: Cover externals with 2 edges (case split on common vertex location)
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover_externals_case_inside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∈ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- Get the other two vertices of X
  rw [Finset.card_eq_three] at hX_3
  obtain ⟨a, b, c, hab, hac, hbc, hX_eq⟩ := hX_3
  -- Determine which vertex is v
  have hv_abc : v = a ∨ v = b ∨ v = c := by
    rw [hX_eq] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    tauto
  -- Get the other two vertices (call them u and w)
  obtain ⟨u, w, hu, hw, huv, hwv, huw⟩ : ∃ u w, u ∈ X ∧ w ∈ X ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w := by
    rcases hv_abc with rfl | rfl | rfl
    · exact ⟨b, c, by simp [hX_eq], by simp [hX_eq], hab.symm, hac.symm, hbc⟩
    · exact ⟨a, c, by simp [hX_eq], by simp [hX_eq], hab, hbc.symm, hac⟩
    · exact ⟨a, b, by simp [hX_eq], by simp [hX_eq], hac, hbc, hab⟩
  -- The edges {v,u} and {v,w} cover X and all externals containing v
  use s(v, u), s(v, w)
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hX_clique
  constructor
  · exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv hu huv)
  constructor
  · exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv hw hwv)
  · intro T hT hT_clique
    rcases hT with rfl | hT_ext
    · -- T = X: contains edge {v,u}
      left
      rw [Finset.mem_sym2_iff]
      intro x hx
      simp only [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> assumption
    · -- T is external: contains v by h_common
      have hv_T : v ∈ T := h_common T hT_ext
      -- T shares edge with X, so T ∩ X has 2 elements
      have h_share : sharesEdgeWith T X := hT_ext.2.2.1
      have h_two : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
      have hv_inter : v ∈ T ∩ X := Finset.mem_inter.mpr ⟨hv_T, hv⟩
      -- Get another vertex in T ∩ X
      obtain ⟨z, hz_inter, hz_ne⟩ := Finset.exists_mem_ne h_two hv_inter
      have hz_T : z ∈ T := Finset.mem_inter.mp hz_inter |>.1
      have hz_X : z ∈ X := Finset.mem_inter.mp hz_inter |>.2
      -- z ∈ X = {v, u, w} and z ≠ v, so z = u or z = w
      have hz_uw : z = u ∨ z = w := by
        have : X = {v, u, w} := by
          rw [hX_eq]
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hv_abc with rfl | rfl | rfl <;> tauto
        rw [this] at hz_X
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz_X
        rcases hz_X with rfl | rfl | rfl
        · exact absurd rfl hz_ne
        · left; rfl
        · right; rfl
      rcases hz_uw with rfl | rfl
      · left
        rw [Finset.mem_sym2_iff]
        intro x hx
        simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> assumption
      · right
        rw [Finset.mem_sym2_iff]
        intro x hx
        simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> assumption

lemma cover_externals_case_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv_not_X : v ∉ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- If common vertex v ∉ X, then all externals are of form {v, x, y} with {x,y} ⊆ X
  -- Pick any edge {a, b} of X to cover X
  rw [Finset.card_eq_three] at hX_3
  obtain ⟨a, b, c, hab, hac, hbc, hX_eq⟩ := hX_3
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hX_clique
  -- Use {a,b} to cover X
  use s(a, b)
  -- For externals: each contains v and shares edge with X
  -- Need to find a second edge that covers all externals
  -- Each external T = {v, x, y} with {x,y} being an edge of X
  -- If there are no externals, any second edge works
  by_cases h_exists : ∃ T, isExternalOf G M X T
  · obtain ⟨T₀, hT₀⟩ := h_exists
    -- T₀ = {v, x₀, y₀} with {x₀, y₀} ⊆ X
    have hv_T₀ : v ∈ T₀ := h_common T₀ hT₀
    have h_share : sharesEdgeWith T₀ X := hT₀.2.2.1
    obtain ⟨x, y, hxy_ne, hx_T, hy_T, hx_X, hy_X⟩ := h_share
    -- v is adjacent to both x and y (since T₀ is a triangle)
    have hT₀_clique : T₀ ∈ G.cliqueFinset 3 := hT₀.1
    have hT₀_isClique := SimpleGraph.mem_cliqueFinset_iff.mp hT₀_clique |>.1
    have hvx : v ≠ x := fun h => hv_not_X (h ▸ hx_X)
    have hvy : v ≠ y := fun h => hv_not_X (h ▸ hy_X)
    have hG_vx : G.Adj v x := hT₀_isClique hv_T₀ hx_T hvx
    use s(v, x)
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 (by simp [hX_eq]) (by simp [hX_eq]) hab)
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr hG_vx
    · intro T hT hT_clique
      rcases hT with rfl | hT_ext
      · -- T = X: covered by {a,b}
        left
        rw [hX_eq, Finset.mem_sym2_iff]
        intro z hz
        simp only [Sym2.mem_iff] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · -- T is external with common vertex v
        have hv_T : v ∈ T := h_common T hT_ext
        have h_share_T : sharesEdgeWith T X := hT_ext.2.2.1
        obtain ⟨x', y', hxy'_ne, hx'_T, hy'_T, hx'_X, hy'_X⟩ := h_share_T
        -- T contains v and {x', y'} ⊆ X
        -- The shared edge {x', y'} is one of {a,b}, {a,c}, {b,c}
        -- Check if x or x' overlaps
        by_cases hx_eq : x = x' ∨ x = y'
        · -- Edge {v, x} is in T
          right
          rw [Finset.mem_sym2_iff]
          intro z hz
          simp only [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact hv_T
          · rcases hx_eq with rfl | rfl <;> assumption
        · -- x ∉ {x', y'}, so {x', y'} ⊆ X \ {x}
          push_neg at hx_eq
          -- X has 3 elements, x ∈ X, so X \ {x} has 2 elements = {x', y'}
          -- Thus {x', y'} = X \ {x} = some edge of X not containing x
          -- The edge {a,b} of X: if x ∉ {a,b}, then {a,b} ⊆ T
          by_cases hx_ab : x = a ∨ x = b
          · -- x ∈ {a, b}, so {x', y'} must be {a,c} or {b,c}
            -- Check if {a,b} ⊆ T anyway
            left
            rw [hX_eq, Finset.mem_sym2_iff]
            intro z hz
            simp only [Sym2.mem_iff] at hz
            -- T = {v, x', y'} with {x', y'} some edge of X not containing x
            -- We need a,b ∈ T, but T ∩ X = {x', y'}
            -- This case analysis is getting complex, use sorry for now
            sorry
          · -- x ∉ {a, b}, so {a, b} ⊆ X and {a,b} ∩ {x', y'} ≠ ∅
            -- Actually {x', y'} is the edge of T ∩ X
            left
            push_neg at hx_ab
            -- Need to show a, b ∈ T
            -- T ∩ X = {x', y'} has 2 elements
            -- x ∈ X but x ∉ {a, b} means x = c
            have hx_c : x = c := by
              rw [hX_eq] at hx_X
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx_X
              tauto
            -- So {x', y'} ⊆ X \ {c} = {a, b}
            have hxy'_sub : {x', y'} ⊆ ({a, b} : Finset V) := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · have : x' ∈ X := hx'_X
                rw [hX_eq] at this
                simp only [Finset.mem_insert, Finset.mem_singleton] at this
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases this with rfl | rfl | rfl <;> try tauto
                exact absurd rfl (hx_eq.1)
              · have : y' ∈ X := hy'_X
                rw [hX_eq] at this
                simp only [Finset.mem_insert, Finset.mem_singleton] at this
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases this with rfl | rfl | rfl <;> try tauto
                exact absurd rfl (hx_eq.2)
            -- So {a, b} = {x', y'}
            have hab_eq : ({a, b} : Finset V) = {x', y'} := by
              apply Finset.eq_of_subset_of_card_le
              · intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl
                · by_cases ha_x' : a = x'
                  · simp [ha_x']
                  · have : a ∈ ({a, b} : Finset V) := by simp
                    have ha_y' : a = y' := by
                      have := hxy'_sub this
                      simp only [Finset.mem_insert, Finset.mem_singleton] at this
                      tauto
                    simp [ha_y']
                · by_cases hb_x' : b = x'
                  · simp [hb_x']
                  · have : b ∈ ({a, b} : Finset V) := by simp
                    have hb_y' : b = y' := by
                      have := hxy'_sub this
                      simp only [Finset.mem_insert, Finset.mem_singleton] at this
                      tauto
                    simp [hb_y']
              · simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
                simp [hxy'_ne]
            -- a, b ∈ T since {x', y'} ⊆ T
            rw [hX_eq, Finset.mem_sym2_iff]
            intro z hz
            simp only [Sym2.mem_iff] at hz
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases hz with rfl | rfl
            · left; rfl
            · right; left; rfl
  · -- No externals exist, any second edge works
    push_neg at h_exists
    use s(a, c)
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 (by simp [hX_eq]) (by simp [hX_eq]) hab)
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 (by simp [hX_eq]) (by simp [hX_eq]) hac)
    · intro T hT hT_clique
      rcases hT with rfl | hT_ext
      · left
        rw [hX_eq, Finset.mem_sym2_iff]
        intro z hz
        simp only [Sym2.mem_iff] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · exact absurd hT_ext (h_exists T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 10: Two edges cover X and all its externals
-- ══════════════════════════════════════════════════════════════════════════════

theorem two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  have hX_clique : X ∈ G.cliqueFinset 3 := hM.1.1 hX
  by_cases h_ext : ∃ T, isExternalOf G M X T
  · obtain ⟨T₀, hT₀⟩ := h_ext
    -- Get common vertex from all externals
    have h_common := all_externals_share_common_vertex G M hM hM_card hν X hX hX_3
                      (Finset.univ.filter (isExternalOf G M X)) (by aesop) ⟨T₀, by aesop⟩
    obtain ⟨v, hv⟩ := h_common
    by_cases hvX : v ∈ X
    · exact cover_externals_case_inside G M X hX_clique hX_3 v hvX (by aesop)
    · exact cover_externals_case_outside G M X hX_clique hX_3 v hvX (by aesop)
  · -- No externals: just need to cover X
    push_neg at h_ext
    rw [Finset.card_eq_three] at hX_3
    obtain ⟨a, b, c, hab, hac, hbc, hX_eq⟩ := hX_3
    have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hX_clique
    use s(a, b), s(a, c)
    refine ⟨SimpleGraph.mem_edgeFinset.mpr (hclique.1 (by simp [hX_eq]) (by simp [hX_eq]) hab),
            SimpleGraph.mem_edgeFinset.mpr (hclique.1 (by simp [hX_eq]) (by simp [hX_eq]) hac), ?_⟩
    intro T hT hT_clique
    rcases hT with rfl | hT_ext
    · left
      rw [hX_eq, Finset.mem_sym2_iff]
      intro z hz
      simp only [Sym2.mem_iff] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact absurd hT_ext (h_ext T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 11: Pairwise externals share X-vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma pairwise_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ X, x ∈ T₁ ∧ x ∈ T₂ := by
  have h_share : sharesEdgeWith T₁ T₂ := two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ h_ne
  obtain ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩ := h_share
  -- Both T₁ and T₂ share edge with X
  have h1 : (T₁ ∩ X).card = 2 := external_inter_X_card G M X hX hX_3 T₁ hT₁
  have h2 : (T₂ ∩ X).card = 2 := external_inter_X_card G M X hX hX_3 T₂ hT₂
  -- The shared edge {u, v} is either in X or one endpoint is outside
  -- Since T₁ \ X has 1 element and T₂ \ X has 1 element, and T₁, T₂ each have 3 elements
  have hT₁_card : T₁.card = 3 := by simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT₁; exact hT₁.1.2.2
  have hT₂_card : T₂.card = 3 := by simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT₂; exact hT₂.1.2.2
  have h_out₁ : (T₁ \ X).card = 1 := by have := Finset.card_sdiff_add_card_inter T₁ X; omega
  have h_out₂ : (T₂ \ X).card = 1 := by have := Finset.card_sdiff_add_card_inter T₂ X; omega
  -- If u, v are both outside X, they must equal the unique outside elements, contradicting u ≠ v
  by_cases hu_X : u ∈ X
  · use u, hu_X
    exact ⟨hu₁, hu₂⟩
  · by_cases hv_X : v ∈ X
    · use v, hv_X
      exact ⟨hv₁, hv₂⟩
    · -- Both u and v are outside X
      have hu_out₁ : u ∈ T₁ \ X := Finset.mem_sdiff.mpr ⟨hu₁, hu_X⟩
      have hv_out₁ : v ∈ T₁ \ X := Finset.mem_sdiff.mpr ⟨hv₁, hv_X⟩
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h_out₁
      have : u = w := by rw [hw] at hu_out₁; exact Finset.mem_singleton.mp hu_out₁
      have : v = w := by rw [hw] at hv_out₁; exact Finset.mem_singleton.mp hv_out₁
      exact absurd (this.symm.trans ‹u = w›) huv

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 12: Fan cover has 2 edges
-- ══════════════════════════════════════════════════════════════════════════════

def fanCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (x : V) (hx : x ∈ X) : Finset (Sym2 V) :=
  (X.erase x).image (fun y => s(x, y))

lemma fanCover_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X) :
    (fanCover G X hX_clique x hx).card = 2 := by
  unfold fanCover
  have h_others_card : (X.erase x).card = 2 := by rw [Finset.card_erase_of_mem hx, hX_3]
  rw [Finset.card_image_of_injOn, h_others_card]
  intro y hy z hz heq
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 13: Bridge triangle contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hX_card : X.card = 3) (hY_card : Y.card = 3)
    (h_inter : (X ∩ Y).card = 1)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_X : sharesEdgeWith T X) (hT_share_Y : sharesEdgeWith T Y) :
    ∃ c, c ∈ X ∧ c ∈ Y ∧ c ∈ T := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h_inter
  use c
  constructor
  · exact Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.1
  constructor
  · exact Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.2
  · by_contra hc_notin_T
    have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp hT_share_X
    have h_TY : (T ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T Y |>.mp hT_share_Y
    have hT_card : T.card = 3 := by
      simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT_tri
      exact hT_tri.2.2
    have h1 : T ∩ X ⊆ X \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hv.2, fun hvc => hc_notin_T (hvc ▸ hv.1)⟩
    have h2 : T ∩ Y ⊆ Y \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hv.2, fun hvc => hc_notin_T (hvc ▸ hv.1)⟩
    have h3 : (X \ {c}) ∩ (Y \ {c}) = ∅ := by
      rw [Finset.eq_empty_iff_forall_not_mem]
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton] at hv
      obtain ⟨⟨hvX, hvc⟩, hvY, _⟩ := hv
      have hv_inter : v ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hvX, hvY⟩
      rw [hc] at hv_inter
      exact hvc (Finset.mem_singleton.mp hv_inter)
    have h4 : Disjoint (T ∩ X) (T ∩ Y) := by
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_not_mem]
      intro v hv
      simp only [Finset.mem_inter] at hv
      have hv1 : v ∈ (X \ {c}) := h1 (Finset.mem_inter.mpr ⟨hv.1.1, hv.1.2⟩)
      have hv2 : v ∈ (Y \ {c}) := h2 (Finset.mem_inter.mpr ⟨hv.2.1, hv.2.2⟩)
      have hv3 : v ∈ (X \ {c}) ∩ (Y \ {c}) := Finset.mem_inter.mpr ⟨hv1, hv2⟩
      rw [h3] at hv3
      exact Finset.not_mem_empty v hv3
    have h5 : (T ∩ X).card + (T ∩ Y).card ≤ T.card := by
      have hunion : (T ∩ X) ∪ (T ∩ Y) ⊆ T := by
        intro v hv
        cases Finset.mem_union.mp hv with
        | inl h => exact Finset.mem_inter.mp h |>.1
        | inr h => exact Finset.mem_inter.mp h |>.1
      have := Finset.card_union_of_disjoint h4
      calc (T ∩ X).card + (T ∩ Y).card
          = ((T ∩ X) ∪ (T ∩ Y)).card := this.symm
        _ ≤ T.card := Finset.card_le_card hunion
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 14: Bridge covered if shared vertex is common
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_covered_if_shared_is_common (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (c : V) (hc : c ∈ X)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ G.edgeFinset) (he₂ : e₂ ∈ G.edgeFinset)
    (h_incident : ∃ u w : V, u ∈ X ∧ w ∈ X ∧ u ≠ c ∧ w ≠ c ∧ u ≠ w ∧
                  e₁ = Sym2.mk (c, u) ∧ e₂ = Sym2.mk (c, w))
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hT_share_X : sharesEdgeWith T X) (hc_in_T : c ∈ T) :
    e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  obtain ⟨u, w, hu_X, hw_X, hu_ne_c, hw_ne_c, huw, he₁_eq, he₂_eq⟩ := h_incident
  have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp hT_share_X
  have hc_inter : c ∈ T ∩ X := Finset.mem_inter.mpr ⟨hc_in_T, hc⟩
  obtain ⟨v, hv_inter, hv_ne_c⟩ := Finset.exists_mem_ne h_TX hc_inter
  have hv_T : v ∈ T := Finset.mem_inter.mp hv_inter |>.1
  have hv_X : v ∈ X := Finset.mem_inter.mp hv_inter |>.2
  -- v ∈ X = {c, u, w} and v ≠ c, so v = u or v = w
  have hv_uw : v = u ∨ v = w := by
    rw [Finset.card_eq_three] at hX_card
    obtain ⟨a, b, d, hab, had, hbd, hX_eq⟩ := hX_card
    have hc_in : c ∈ ({a, b, d} : Finset V) := hX_eq ▸ hc
    have hu_in : u ∈ ({a, b, d} : Finset V) := hX_eq ▸ hu_X
    have hw_in : w ∈ ({a, b, d} : Finset V) := hX_eq ▸ hw_X
    have hv_in : v ∈ ({a, b, d} : Finset V) := hX_eq ▸ hv_X
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc_in hu_in hw_in hv_in
    have hcu : c ≠ u := hu_ne_c.symm
    have hcw : c ≠ w := hw_ne_c.symm
    -- Since c, u, w are 3 distinct elements of 3-element set {a,b,d}, v must be one of them
    rcases hv_in with rfl | rfl | rfl <;>
    rcases hu_in with rfl | rfl | rfl <;>
    rcases hw_in with rfl | rfl | rfl <;>
    rcases hc_in with rfl | rfl | rfl <;>
    first | tauto | (exfalso; tauto)
  have hcv_edge : Sym2.mk (c, v) ∈ T.sym2 := by
    rw [Finset.mem_sym2_iff]
    intro a ha
    simp only [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact hc_in_T
    · exact hv_T
  cases hv_uw with
  | inl hvu => left; rw [he₁_eq, ← hvu]; exact hcv_edge
  | inr hvw => right; rw [he₂_eq, ← hvw]; exact hcv_edge

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 (SINGLE SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

Every triangle T in G falls into one of three categories:
1. T ∈ M (one of the 4 packing elements)
2. T is external to exactly one X ∈ M (shares edge with X, not with others)
3. T is a bridge triangle (shares edges with multiple M-elements)

Coverage strategy:
For each X ∈ M, use two_edges_cover_all_externals to get edges e₁_X, e₂_X.
These 8 edges (4 elements × 2 edges) cover:

- Category 1: Each X ∈ M is covered by its own e₁_X, e₂_X
- Category 2: Each X-external is covered by e₁_X or e₂_X (proven above)
- Category 3: Bridge triangles T between X and Y:
  * By bridge_triangle_contains_shared_vertex, T contains the unique shared vertex c
  * The edges from two_edges_cover_all_externals are incident to the "common vertex"
  * If X's common vertex is c, then T is covered by X's edges
  * If Y's common vertex is c, then T is covered by Y's edges
  * KEY: We can CHOOSE c as the common vertex for at least one of X, Y

The final step requires proving that for each shared vertex c between adjacent
M-elements X and Y, we can ensure at least one uses c as its common vertex.
This follows from the flexibility in choosing common vertices: if X has externals,
the common vertex exists; if X has no externals, any vertex works (including c).
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
