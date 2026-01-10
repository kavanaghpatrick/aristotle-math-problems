/-
  slot323: τ ≤ 8 for ν = 4 - Combined Approach

  KEY INSIGHT: The naive "2 edges from X" construction fails when X has
  externals on all 3 edges. In that case, there's no fan apex IN X.

  SOLUTION: Use common_external_vertex to get apex OUTSIDE X.

  For X with externals on all 3 edges:
  - By common_external_vertex, all externals share vertex t ∉ X
  - Cover: {s(a,t), s(b,c)} covers X and all externals

  This file combines slot319's helpers with slot321's common_external_vertex.
-/

import Mathlib

set_option maxHeartbeats 800000
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
-- BASIC HELPERS (from slot319)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨h u (Sym2.mem_iff.mpr (Or.inl rfl)), h v (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

lemma external_inter_card_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  have hT_card : T.card = 3 := triangle_card_three G T hT.1
  have h_share : sharesEdgeWith T X := hT.2.2.1
  have h_inter_ge : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
  have h_inter_le : (T ∩ X).card ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by
        have h1 : (T ∩ X).card ≤ T.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by
        have h1 : (T ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.1
    have h_eq : T = X := Finset.Subset.antisymm h_sub h_sub'
    exact hT.2.1 (h_eq ▸ hX_in_M)
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- TWO EXTERNALS SHARE EDGE (from slot321)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If T₁, T₂ are distinct X-externals that don't share an edge, then
M' = {T₁, T₂} ∪ (M \ {X}) is a packing of size 5, contradiction.
-/
lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  have hT₁_3 : T₁.card = 3 := triangle_card_three G T₁ hT₁.1
  have hT₂_3 : T₂.card = 3 := triangle_card_three G T₂ hT₂.1
  let M' := {T₁, T₂} ∪ M.erase X
  have hM'_card : M'.card = 5 := by
    have hT₁_not_M : T₁ ∉ M := hT₁.2.1
    have hT₂_not_M : T₂ ∉ M := hT₂.2.1
    have hM_minus_X_card : (M.erase X).card = 3 := by rw [Finset.card_erase_of_mem hX]; omega
    have hT₁_not_MX : T₁ ∉ M.erase X := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MX : T₂ ∉ M.erase X := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem]; simp [h_ne]; simp [h_ne]
    have h_disj : Disjoint {T₁, T₂} (M.erase X) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact fun h => hT₁_not_MX (h ▸ hy);
                                    exact fun h => hT₂_not_MX (h ▸ hy)]
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_X_card]
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht_pair | ht_MX
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MX).2
    · intro t₁ ht₁ t₂ ht₂ h_ne'
      have h_not_share : ∀ t m : Finset V, t.card = 3 → m.card = 3 → ¬sharesEdgeWith t m → (t ∩ m).card ≤ 1 := by
        intro t m ht hm h_ns
        by_contra h
        push_neg at h
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
        exact h_ns ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩
      rcases Finset.mem_union.mp ht₁ with ht₁_pair | ht₁_MX <;>
      rcases Finset.mem_union.mp ht₂ with ht₂_pair | ht₂_MX
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne'
          · rw [Finset.mem_singleton] at ht₂_sing; rw [heq₁, ht₂_sing]
            exact h_not_share T₁ T₂ hT₁_3 hT₂_3 h_no_edge
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂, Finset.inter_comm]
            exact h_not_share T₁ T₂ hT₁_3 hT₂_3 h_no_edge
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne'
      · have hY_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MX).2
        have hY_ne_X : t₂ ≠ X := (Finset.mem_erase.mp ht₂_MX).1
        have hY_3 : t₂.card = 3 := triangle_card_three G t₂ (hM.1.1 hY_M)
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]
          have h_not_share' := hT₁.2.2.2 t₂ hY_M hY_ne_X
          exact h_not_share T₁ t₂ hT₁_3 hY_3 h_not_share'
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          have h_not_share' := hT₂.2.2.2 t₂ hY_M hY_ne_X
          exact h_not_share T₂ t₂ hT₂_3 hY_3 h_not_share'
      · have hY_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MX).2
        have hY_ne_X : t₁ ≠ X := (Finset.mem_erase.mp ht₁_MX).1
        have hY_3 : t₁.card = 3 := triangle_card_three G t₁ (hM.1.1 hY_M)
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂, Finset.inter_comm]
          have h_not_share' := hT₁.2.2.2 t₁ hY_M hY_ne_X
          exact h_not_share T₁ t₁ hT₁_3 hY_3 h_not_share'
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing, Finset.inter_comm]
          have h_not_share' := hT₂.2.2.2 t₁ hY_M hY_ne_X
          exact h_not_share T₂ t₁ hT₂_3 hY_3 h_not_share'
      · exact hM.1.2 (Finset.mem_erase.mp ht₁_MX).2 (Finset.mem_erase.mp ht₂_MX).2 h_ne'
  have h_bound := hν M' hM'_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- COMMON EXTERNAL VERTEX (from slot321)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If T₁, T₂ are X-externals on DIFFERENT edges of X, they share t ∉ X.
- T₁ ∩ X and T₂ ∩ X are different 2-subsets → intersection has 1 element
- By two_externals_share_edge, T₁ ∩ T₂ ≥ 2
- So the extra intersection must come from outside X
-/
lemma common_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂)
    (h_diff_edge : T₁ ∩ X ≠ T₂ ∩ X) :
    ∃ t, t ∉ X ∧ t ∈ T₁ ∧ t ∈ T₂ := by
  have h_share : sharesEdgeWith T₁ T₂ := two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_ge_2 : (T₁ ∩ T₂).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂ |>.mp h_share
  have hT₁X_card : (T₁ ∩ X).card = 2 := external_inter_card_two G M X hX hX_card T₁ hT₁
  have hT₂X_card : (T₂ ∩ X).card = 2 := external_inter_card_two G M X hX hX_card T₂ hT₂
  have h_X_inter_card : ((T₁ ∩ X) ∩ (T₂ ∩ X)).card = 1 := by
    have h_sub1 : (T₁ ∩ X) ∩ (T₂ ∩ X) ⊆ X := fun v hv =>
      Finset.mem_of_mem_inter_right (Finset.mem_of_mem_inter_left hv)
    have h_nonempty : ((T₁ ∩ X) ∩ (T₂ ∩ X)).Nonempty := by
      by_contra h_empty
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      have h_disj : Disjoint (T₁ ∩ X) (T₂ ∩ X) := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
      have h_union_card : ((T₁ ∩ X) ∪ (T₂ ∩ X)).card = 4 := by
        rw [Finset.card_union_of_disjoint h_disj]; omega
      have h_union_sub : (T₁ ∩ X) ∪ (T₂ ∩ X) ⊆ X := fun v hv =>
        match Finset.mem_union.mp hv with
        | Or.inl h => Finset.mem_of_mem_inter_right h
        | Or.inr h => Finset.mem_of_mem_inter_right h
      have := Finset.card_le_card h_union_sub; omega
    have h_card_ge_1 : 1 ≤ ((T₁ ∩ X) ∩ (T₂ ∩ X)).card := Finset.card_pos.mpr h_nonempty
    by_contra h_ne_1
    have h_card_ge_2 : 2 ≤ ((T₁ ∩ X) ∩ (T₂ ∩ X)).card := by omega
    have h_sub1' : (T₁ ∩ X) ∩ (T₂ ∩ X) ⊆ T₁ ∩ X := Finset.inter_subset_left
    have h_sub2' : (T₁ ∩ X) ∩ (T₂ ∩ X) ⊆ T₂ ∩ X := Finset.inter_subset_right
    have h_eq : T₁ ∩ X = T₂ ∩ X := by
      have h_eq1 : (T₁ ∩ X) ∩ (T₂ ∩ X) = T₁ ∩ X := by
        apply Finset.eq_of_subset_of_card_le h_sub1'
        have := Finset.card_le_card h_sub1'; omega
      have h_eq2 : (T₁ ∩ X) ∩ (T₂ ∩ X) = T₂ ∩ X := by
        apply Finset.eq_of_subset_of_card_le h_sub2'
        have := Finset.card_le_card h_sub2'; omega
      rw [← h_eq1, h_eq2]
    exact h_diff_edge h_eq
  have hT₁_card : T₁.card = 3 := triangle_card_three G T₁ hT₁.1
  have hT₂_card : T₂.card = 3 := triangle_card_three G T₂ hT₂.1
  have hT₁_ext_card : (T₁ \ X).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter T₁ X; omega
  have hT₂_ext_card : (T₂ \ X).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter T₂ X; omega
  obtain ⟨t₁, ht₁⟩ := Finset.card_eq_one.mp hT₁_ext_card
  obtain ⟨t₂, ht₂⟩ := Finset.card_eq_one.mp hT₂_ext_card
  have h_t1_in_T1 : t₁ ∈ T₁ := by
    have : t₁ ∈ T₁ \ X := by rw [ht₁]; exact Finset.mem_singleton_self t₁
    exact (Finset.mem_sdiff.mp this).1
  have h_t2_in_T2 : t₂ ∈ T₂ := by
    have : t₂ ∈ T₂ \ X := by rw [ht₂]; exact Finset.mem_singleton_self t₂
    exact (Finset.mem_sdiff.mp this).1
  have h_t1_notin_X : t₁ ∉ X := by
    have : t₁ ∈ T₁ \ X := by rw [ht₁]; exact Finset.mem_singleton_self t₁
    exact (Finset.mem_sdiff.mp this).2
  have h_t2_notin_X : t₂ ∉ X := by
    have : t₂ ∈ T₂ \ X := by rw [ht₂]; exact Finset.mem_singleton_self t₂
    exact (Finset.mem_sdiff.mp this).2
  have h_t_eq : t₁ = t₂ := by
    by_contra h_ne_t
    have h_inter_sub_X : T₁ ∩ T₂ ⊆ X := by
      intro v hv
      have hv_T1 : v ∈ T₁ := Finset.mem_of_mem_inter_left hv
      have hv_T2 : v ∈ T₂ := Finset.mem_of_mem_inter_right hv
      by_contra hv_notin_X
      have hv_eq_t1 : v = t₁ := by
        have hv_sdiff : v ∈ T₁ \ X := Finset.mem_sdiff.mpr ⟨hv_T1, hv_notin_X⟩
        rw [ht₁] at hv_sdiff
        exact Finset.mem_singleton.mp hv_sdiff
      have hv_eq_t2 : v = t₂ := by
        have hv_sdiff : v ∈ T₂ \ X := Finset.mem_sdiff.mpr ⟨hv_T2, hv_notin_X⟩
        rw [ht₂] at hv_sdiff
        exact Finset.mem_singleton.mp hv_sdiff
      exact h_ne_t (hv_eq_t1.symm.trans hv_eq_t2)
    have h_sub : T₁ ∩ T₂ ⊆ (T₁ ∩ X) ∩ (T₂ ∩ X) := fun v hv =>
      Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_of_mem_inter_left hv, h_inter_sub_X hv⟩,
                             Finset.mem_inter.mpr ⟨Finset.mem_of_mem_inter_right hv, h_inter_sub_X hv⟩⟩
    have h_card_le : (T₁ ∩ T₂).card ≤ ((T₁ ∩ X) ∩ (T₂ ∩ X)).card := Finset.card_le_card h_sub
    omega
  use t₁
  exact ⟨h_t1_notin_X, h_t1_in_T1, h_t_eq ▸ h_t2_in_T2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE TRIANGLES (from slot319)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ (∃ X ∈ M, isExternalOf G M X T) ∨ isBridgeTriangle G M T := by
  by_cases hT_in : T ∈ M
  · left; exact hT_in
  · right
    obtain ⟨X, hX_in, hX_share⟩ := nonpacking_shares_edge G M hM T hT hT_in
    by_cases h_unique : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
    · left; exact ⟨X, hX_in, hT, hT_in, hX_share, h_unique⟩
    · right
      push_neg at h_unique
      obtain ⟨Y, hY_in, hY_ne, hY_share⟩ := h_unique
      exact ⟨hT, hT_in, X, Y, hX_in, hY_in, hY_ne.symm, hX_share, hY_share⟩

lemma bridge_covered_by_some_m_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V)
    (hT : isBridgeTriangle G M T) :
    ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  obtain ⟨_, _, X, Y, hX_in, _, _, hX_share, _⟩ := hT
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hX_share
  exact ⟨X, hX_in, u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

For each X ∈ M, we construct at most 2 edges that cover X and all X-externals.

CASE ANALYSIS for X = {a, b, c}:

Case 1: X has externals on at most 2 edges of X
  - The externals share a common vertex v ∈ X (by pigeonhole on 2-subsets)
  - Cover: {s(v, other1), s(v, other2)} where {other1, other2} = X \ {v}
  - This covers X and all externals (they all contain v)

Case 2: X has externals on all 3 edges of X
  - There is NO common vertex in X (since {a,b} ∩ {a,c} ∩ {b,c} = ∅)
  - But by common_external_vertex, all externals share t ∉ X
  - Cover: {s(a, t), s(b, c)} covers:
    * X via s(b, c)
    * External on {a,b}: {a,b,t} via s(a,t)
    * External on {a,c}: {a,c,t} via s(a,t)
    * External on {b,c}: {b,c,t} via s(b,c)

Bridges are covered by some M-element's edges (bridge_covered_by_some_m_edge).

Total: 4 × 2 = 8 edges.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
