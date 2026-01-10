/-
  slot325: Prove universal_apex_exists (SINGLE TARGET)

  STRATEGY: Case split by number of "supported edges" (edges of X with externals)

  Case 0: No externals → trivially true (first disjunct)
  Case 1-2: All externals on ≤2 edges → by pigeonhole, common v ∈ X exists
  Case 3: Externals on all 3 edges → use common_external_vertex for t ∉ X

  All 14 proven helpers from slot319/321 included.
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS (slot319/321 - Aristotle verified)
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

lemma external_inter_card_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  have hT_card : T.card = 3 := triangle_card_three G T hT.1
  have h_share : sharesEdgeWith T X := hT.2.2.1
  have h_inter_ge : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
  have h_inter_le : (T ∩ X).card ≤ 2 := by
    by_contra h_gt; push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).1
    exact hT.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hX_in_M)
  omega

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
        by_contra h; push_neg at h
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

-- PAIRWISE: Two externals share v ∈ X (proven by slot319)
lemma two_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_card : X.card = 3) (hX_in : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂) :
    ∃ v ∈ X, v ∈ T₁ ∧ v ∈ T₂ := by
  have h1 : (T₁ ∩ X).card = 2 := external_inter_card_two G M X hX_in hX_card T₁ hT₁
  have h2 : (T₂ ∩ X).card = 2 := external_inter_card_two G M X hX_in hX_card T₂ hT₂
  have h_inter_nonempty : ((T₁ ∩ X) ∩ (T₂ ∩ X)).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have h_disj : Disjoint (T₁ ∩ X) (T₂ ∩ X) := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
    have h_union_sub : (T₁ ∩ X) ∪ (T₂ ∩ X) ⊆ X := fun v hv =>
      match Finset.mem_union.mp hv with
      | Or.inl h => Finset.mem_of_mem_inter_right h
      | Or.inr h => Finset.mem_of_mem_inter_right h
    have h_union_card : ((T₁ ∩ X) ∪ (T₂ ∩ X)).card = 4 := by
      rw [Finset.card_union_of_disjoint h_disj]; omega
    have := Finset.card_le_card h_union_sub; omega
  obtain ⟨v, hv⟩ := h_inter_nonempty
  exact ⟨v, Finset.mem_of_mem_inter_right (Finset.mem_of_mem_inter_left hv),
         Finset.mem_of_mem_inter_left (Finset.mem_of_mem_inter_left hv),
         Finset.mem_of_mem_inter_left (Finset.mem_of_mem_inter_right hv)⟩

-- KEY: Different-edge externals share t ∉ X (proven by slot321)
lemma common_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) (h_diff_edge : T₁ ∩ X ≠ T₂ ∩ X) :
    ∃ t, t ∉ X ∧ t ∈ T₁ ∧ t ∈ T₂ := by
  have h_share : sharesEdgeWith T₁ T₂ := two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_ge_2 : (T₁ ∩ T₂).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂ |>.mp h_share
  have hT₁X_card : (T₁ ∩ X).card = 2 := external_inter_card_two G M X hX hX_card T₁ hT₁
  have hT₂X_card : (T₂ ∩ X).card = 2 := external_inter_card_two G M X hX hX_card T₂ hT₂
  have h_X_inter_card : ((T₁ ∩ X) ∩ (T₂ ∩ X)).card = 1 := by
    have h_nonempty : ((T₁ ∩ X) ∩ (T₂ ∩ X)).Nonempty := by
      by_contra h_empty
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      have h_disj : Disjoint (T₁ ∩ X) (T₂ ∩ X) := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
      have h_union_sub : (T₁ ∩ X) ∪ (T₂ ∩ X) ⊆ X := fun v hv =>
        match Finset.mem_union.mp hv with
        | Or.inl h => Finset.mem_of_mem_inter_right h
        | Or.inr h => Finset.mem_of_mem_inter_right h
      have h_union_card : ((T₁ ∩ X) ∪ (T₂ ∩ X)).card = 4 := by
        rw [Finset.card_union_of_disjoint h_disj]; omega
      have := Finset.card_le_card h_union_sub; omega
    have h_card_ge_1 : 1 ≤ ((T₁ ∩ X) ∩ (T₂ ∩ X)).card := Finset.card_pos.mpr h_nonempty
    by_contra h_ne_1
    have h_card_ge_2 : 2 ≤ ((T₁ ∩ X) ∩ (T₂ ∩ X)).card := by omega
    have h_sub1 : (T₁ ∩ X) ∩ (T₂ ∩ X) ⊆ T₁ ∩ X := Finset.inter_subset_left
    have h_sub2 : (T₁ ∩ X) ∩ (T₂ ∩ X) ⊆ T₂ ∩ X := Finset.inter_subset_right
    have h_eq : T₁ ∩ X = T₂ ∩ X := by
      have h_eq1 : (T₁ ∩ X) ∩ (T₂ ∩ X) = T₁ ∩ X := by
        apply Finset.eq_of_subset_of_card_le h_sub1
        have := Finset.card_le_card h_sub1; omega
      have h_eq2 : (T₁ ∩ X) ∩ (T₂ ∩ X) = T₂ ∩ X := by
        apply Finset.eq_of_subset_of_card_le h_sub2
        have := Finset.card_le_card h_sub2; omega
      rw [← h_eq1, h_eq2]
    exact h_diff_edge h_eq
  have hT₁_card : T₁.card = 3 := triangle_card_three G T₁ hT₁.1
  have hT₂_card : T₂.card = 3 := triangle_card_three G T₂ hT₂.1
  have hT₁_ext_card : (T₁ \ X).card = 1 := by have h := Finset.card_sdiff_add_card_inter T₁ X; omega
  have hT₂_ext_card : (T₂ \ X).card = 1 := by have h := Finset.card_sdiff_add_card_inter T₂ X; omega
  obtain ⟨t₁, ht₁⟩ := Finset.card_eq_one.mp hT₁_ext_card
  obtain ⟨t₂, ht₂⟩ := Finset.card_eq_one.mp hT₂_ext_card
  have h_t1_in_T1 : t₁ ∈ T₁ := (Finset.mem_sdiff.mp (ht₁ ▸ Finset.mem_singleton_self t₁)).1
  have h_t2_in_T2 : t₂ ∈ T₂ := (Finset.mem_sdiff.mp (ht₂ ▸ Finset.mem_singleton_self t₂)).1
  have h_t1_notin_X : t₁ ∉ X := (Finset.mem_sdiff.mp (ht₁ ▸ Finset.mem_singleton_self t₁)).2
  have h_t2_notin_X : t₂ ∉ X := (Finset.mem_sdiff.mp (ht₂ ▸ Finset.mem_singleton_self t₂)).2
  have h_t_eq : t₁ = t₂ := by
    by_contra h_ne_t
    have h_inter_sub_X : T₁ ∩ T₂ ⊆ X := by
      intro v hv
      have hv_T1 : v ∈ T₁ := Finset.mem_of_mem_inter_left hv
      have hv_T2 : v ∈ T₂ := Finset.mem_of_mem_inter_right hv
      by_contra hv_notin_X
      have hv_eq_t1 : v = t₁ := Finset.mem_singleton.mp (ht₁ ▸ Finset.mem_sdiff.mpr ⟨hv_T1, hv_notin_X⟩)
      have hv_eq_t2 : v = t₂ := Finset.mem_singleton.mp (ht₂ ▸ Finset.mem_sdiff.mpr ⟨hv_T2, hv_notin_X⟩)
      exact h_ne_t (hv_eq_t1.symm.trans hv_eq_t2)
    have h_sub : T₁ ∩ T₂ ⊆ (T₁ ∩ X) ∩ (T₂ ∩ X) := fun v hv =>
      Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_of_mem_inter_left hv, h_inter_sub_X hv⟩,
                             Finset.mem_inter.mpr ⟨Finset.mem_of_mem_inter_right hv, h_inter_sub_X hv⟩⟩
    have := Finset.card_le_card h_sub; omega
  use t₁
  exact ⟨h_t1_notin_X, h_t1_in_T1, h_t_eq ▸ h_t2_in_T2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: universal_apex_exists (SINGLE SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for universal_apex_exists:

For X = {a, b, c}, externals have T ∩ X ∈ {{a,b}, {a,c}, {b,c}}.

Case analysis by number of distinct "supported edges" (edges with externals):

CASE 0: No externals exist
  → First disjunct holds trivially

CASE 1: All externals on same edge (say {a,b})
  → Both a and b are in all externals
  → Pick apex = a (middle disjunct with v = a)

CASE 2: Externals on exactly 2 edges (say {a,b} and {a,c})
  → {a,b} ∩ {a,c} = {a}
  → Vertex a is in all externals (middle disjunct)

CASE 3: Externals on all 3 edges ({a,b}, {a,c}, {b,c})
  → No vertex of X is in all three ({a,b} ∩ {a,c} ∩ {b,c} = ∅)
  → But by common_external_vertex, any two on different edges share t ∉ X
  → Since all pairs share the SAME t (apply transitively), t is universal apex
  → Third disjunct holds with this t
-/
lemma universal_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    (∀ T, isExternalOf G M X T → False) ∨  -- No externals
    (∃ v ∈ X, ∀ T, isExternalOf G M X T → v ∈ T) ∨  -- Apex in X
    (∃ t, t ∉ X ∧ ∀ T, isExternalOf G M X T → t ∈ T)  -- Apex outside X
    := by
  sorry

end
