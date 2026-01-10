/-
  slot329: CONSOLIDATED PROVEN LEMMAS for τ ≤ 8

  All lemmas proven by Aristotle (0 sorry) from slots 325, 326, 328.
  This file contains the complete proven scaffolding.

  PROVEN:
  - universal_apex_exists
  - two_edges_cover_X_and_externals
  - common_vertex_of_external_triangles_with_distinct_edges
  - externals_disjoint_implies_false_v2
  - bridge_covered_by_some_m_edge
  - triangle_classification
  - All helper lemmas

  TARGET: bridge_covered_by_selected_edges (the missing piece for tau_le_8)
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
-- PROVEN HELPERS (Aristotle verified - 0 sorry)
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
    · right; push_neg at h_unique
      obtain ⟨Y, hY_in, hY_ne, hY_share⟩ := h_unique
      exact ⟨hT, hT_in, X, Y, hX_in, hY_in, hY_ne.symm, hX_share, hY_share⟩

lemma bridge_covered_by_some_m_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (hT : isBridgeTriangle G M T) :
    ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  obtain ⟨_, _, X, _, hX_in, _, _, hX_share, _⟩ := hT
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hX_share
  exact ⟨X, hX_in, u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: externals_disjoint_implies_false (Aristotle - slot326)
-- ══════════════════════════════════════════════════════════════════════════════

lemma externals_disjoint_implies_false_v2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T1 T2 : Finset V)
    (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2)
    (h_disj : (T1 ∩ T2).card ≤ 1) : False := by
      have hM'_pack : isTrianglePacking G ((M.erase X) ∪ {T1, T2}) := by
        have hM'_pack : ∀ x ∈ ((M.erase X) ∪ {T1, T2}), x ∈ G.cliqueFinset 3 := by
          simp_all +decide [ isExternalOf ];
          exact fun a ha ha' => by have := hM.1.1 ha'; aesop;
        have hM'_pack : ∀ x ∈ ((M.erase X) ∪ {T1, T2}), ∀ y ∈ ((M.erase X) ∪ {T1, T2}), x ≠ y → (x ∩ y).card ≤ 1 := by
          have hT1_T2 : ∀ a ∈ M, a ≠ X → (T1 ∩ a).card ≤ 1 ∧ (T2 ∩ a).card ≤ 1 := by
            intro a ha haX
            have hT1_a : ¬sharesEdgeWith T1 a := by
              exact hT1.2.2.2 a ha haX
            have hT2_a : ¬sharesEdgeWith T2 a := by
              exact hT2.2.2.2 a ha haX;
            exact ⟨ not_lt.1 fun contra => hT1_a <| sharesEdgeWith_iff_card_inter_ge_two _ _ |>.2 contra, not_lt.1 fun contra => hT2_a <| sharesEdgeWith_iff_card_inter_ge_two _ _ |>.2 contra ⟩;
          have hM'_pack : ∀ x ∈ M.erase X, ∀ y ∈ M.erase X, x ≠ y → (x ∩ y).card ≤ 1 := by
            have := hM.1.2; aesop;
          simp_all +decide [ Finset.inter_comm ];
        exact ⟨ by aesop_cat, by exact fun x hx y hy hxy => if h : x = y then by aesop else hM'_pack x hx y hy h ⟩;
      have hM'_card : ((M.erase X) ∪ {T1, T2}).card > 4 := by
        have hT1_not_in_M : T1 ∉ M := by
          exact hT1.2.1
        have hT2_not_in_M : T2 ∉ M := by
          exact hT2.2.1;
        by_cases hT1_eq_T2 : T1 = T2 <;> simp_all +decide [ Finset.inter_comm ];
        have := hT2.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact h_disj.not_lt ( by rw [ SimpleGraph.isNClique_iff ] at this; aesop );
      exact not_le_of_gt hM'_card ( hν _ hM'_pack )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: common_vertex_of_external_triangles (Aristotle - slot326)
-- ══════════════════════════════════════════════════════════════════════════════

lemma common_vertex_of_external_triangles_with_distinct_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (T1 T2 : Finset V)
    (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2)
    (h_diff_inter : T1 ∩ X ≠ T2 ∩ X) :
    ∃ u, u ∉ X ∧ ∀ T, isExternalOf G M X T → u ∈ T := by
      have h_exists_u : ∃ u, u ∉ X ∧ u ∈ T1 ∧ u ∈ T2 := by
        have h_exists_u : (T1 ∩ T2).card ≥ 2 := by
          contrapose! h_diff_inter;
          have := externals_disjoint_implies_false_v2 G M hM hM_card hν X hX T1 T2 hT1 hT2 ( by linarith ) ; aesop;
        have h_exists_u : (T1 ∩ T2 ∩ X).card ≤ 1 := by
          have h_exists_u : (T1 ∩ X).card = 2 ∧ (T2 ∩ X).card = 2 := by
            exact ⟨ external_inter_card_two G M X hX hX_card T1 hT1, external_inter_card_two G M X hX hX_card T2 hT2 ⟩;
          have h_exists_u : (T1 ∩ X ∩ (T2 ∩ X)).card ≤ 1 := by
            have h_exists_u : (T1 ∩ X ∩ (T2 ∩ X)).card < (T1 ∩ X).card := by
              refine' Finset.card_lt_card _;
              simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
              contrapose! h_diff_inter;
              exact Finset.eq_of_subset_of_card_le ( fun x hx => by aesop ) ( by aesop );
            linarith;
          convert h_exists_u using 2 ; ext ; aesop;
        contrapose! h_exists_u;
        rw [ show T1 ∩ T2 ∩ X = T1 ∩ T2 from Finset.ext fun x => by by_cases hx : x ∈ X <;> aesop ] ; linarith;
      obtain ⟨ u, huX, huT1, huT2 ⟩ := h_exists_u;
      use u, huX;
      intro T hT
      by_contra h_contra
      have h_contra_T1 : (T1 ∩ T).card ≥ 2 := by
        have h_contra_T1 : (T1 ∩ T).card ≥ 2 := by
          have h_contra_T1 : ¬(T1 ∩ T).card ≤ 1 := by
            apply externals_disjoint_implies_false_v2 G M hM hM_card hν X hX T1 T hT1 hT
          exact not_le.mp h_contra_T1
        exact h_contra_T1
      have h_contra_T2 : (T2 ∩ T).card ≥ 2 := by
        have := externals_disjoint_implies_false_v2 G M hM hM_card hν X hX T2 T hT2 hT; aesop;
      have h_contra_X : (T1 ∩ X) ⊆ T ∧ (T2 ∩ X) ⊆ T := by
        have h_contra_X : (T1 ∩ T) ⊆ (T1 ∩ X) ∪ {u} ∧ (T2 ∩ T) ⊆ (T2 ∩ X) ∪ {u} := by
          have h_contra_X : (T1 \ X).card = 1 ∧ (T2 \ X).card = 1 := by
            have := external_inter_card_two G M X hX hX_card T1 hT1; have := external_inter_card_two G M X hX hX_card T2 hT2; simp_all +decide [ Finset.card_sdiff ] ;
            have := hT1.1; have := hT2.1; simp_all +decide [ Finset.inter_comm ] ;
            have := ‹G.IsNClique 3 T1›.2; have := ‹G.IsNClique 3 T2›.2; aesop;
          simp_all +decide [ Finset.card_eq_one ];
          simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
          grind +ring;
        have h_contra_X : (T1 ∩ T) ⊆ (T1 ∩ X) ∧ (T2 ∩ T) ⊆ (T2 ∩ X) := by
          exact ⟨ fun x hx => by have := h_contra_X.1 hx; aesop, fun x hx => by have := h_contra_X.2 hx; aesop ⟩;
        have h_contra_X_card : (T1 ∩ T).card = (T1 ∩ X).card ∧ (T2 ∩ T).card = (T2 ∩ X).card := by
          exact ⟨ le_antisymm ( Finset.card_le_card h_contra_X.1 ) ( by linarith [ external_inter_card_two G M X hX hX_card T1 hT1 ] ), le_antisymm ( Finset.card_le_card h_contra_X.2 ) ( by linarith [ external_inter_card_two G M X hX hX_card T2 hT2 ] ) ⟩;
        have h_contra_X_eq : T1 ∩ T = T1 ∩ X ∧ T2 ∩ T = T2 ∩ X := by
          exact ⟨ Finset.eq_of_subset_of_card_le h_contra_X.1 h_contra_X_card.1.ge, Finset.eq_of_subset_of_card_le h_contra_X.2 h_contra_X_card.2.ge ⟩;
        grind
      have h_contra_X_card : (T ∩ X).card ≥ 3 := by
        have h_contra_X_card : (T1 ∩ X) ∪ (T2 ∩ X) ⊆ T ∩ X := by
          grind;
        have h_contra_X_card : (T1 ∩ X).card = 2 ∧ (T2 ∩ X).card = 2 := by
          exact ⟨ external_inter_card_two G M X hX hX_card T1 hT1, external_inter_card_two G M X hX hX_card T2 hT2 ⟩;
        have h_contra_X_card : (T1 ∩ X ∪ T2 ∩ X).card ≥ 3 := by
          have h_contra_X_card : (T1 ∩ X ∩ (T2 ∩ X)).card < 2 := by
            exact lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( show T1 ∩ X ∩ ( T2 ∩ X ) ⊆ T1 ∩ X from Finset.inter_subset_left ) ) h_contra_X_card.1.le ) fun h => h_diff_inter <| Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith ) |> fun h' => h'.symm.trans <| Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by linarith );
          grind;
        exact h_contra_X_card.trans ( Finset.card_mono ‹_› )
      have h_contra_X_card_eq : (T ∩ X).card = 2 := by
        apply external_inter_card_two G M X hX hX_card T hT
      linarith [h_contra_X_card, h_contra_X_card_eq]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: universal_apex_exists (Aristotle - slot325/326)
-- ══════════════════════════════════════════════════════════════════════════════

lemma universal_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    (∀ T, isExternalOf G M X T → False) ∨
    (∃ v ∈ X, ∀ T, isExternalOf G M X T → v ∈ T) ∨
    (∃ t, t ∉ X ∧ ∀ T, isExternalOf G M X T → t ∈ T) := by
  by_cases h : ∃ T : Finset V, isExternalOf G M X T <;> simp_all +decide [ Classical.not_forall ];
  by_cases h₂ : ∃ T1 T2 : Finset V, isExternalOf G M X T1 ∧ isExternalOf G M X T2 ∧ T1 ∩ X ≠ T2 ∩ X;
  · obtain ⟨ T1, T2, hT1, hT2, hne ⟩ := h₂;
    exact Or.inr <| Or.inr <| by obtain ⟨ u, hu₁, hu₂ ⟩ := common_vertex_of_external_triangles_with_distinct_edges G M hM hM_card hν X hX hX_card T1 T2 hT1 hT2 hne; exact ⟨ u, hu₁, hu₂ ⟩ ;
  · obtain ⟨ T, hT ⟩ := h;
    obtain ⟨E, hE⟩ : ∃ E : Finset V, ∀ T : Finset V, isExternalOf G M X T → T ∩ X = E := by
      exact ⟨ T ∩ X, fun T' hT' => Classical.not_not.1 fun h => h₂ ⟨ T', T, hT', hT, h ⟩ ⟩;
    obtain ⟨v, hv⟩ : ∃ v ∈ E, v ∈ X := by
      have := hE T hT; rw [ ← this ] ; exact Exists.elim ( Finset.card_pos.mp ( by linarith [ external_inter_card_two G M X hX ( by linarith ) T hT ] ) ) fun x hx => ⟨ x, hx, Finset.mem_of_mem_inter_right hx ⟩ ;
    exact Or.inr <| Or.inl ⟨ v, hv.2, fun T hT => Finset.mem_of_mem_inter_left <| hE T hT ▸ hv.1 ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: three_set_decomp (Aristotle - slot326)
-- ══════════════════════════════════════════════════════════════════════════════

lemma three_set_decomp (X : Finset V) (hX : X.card = 3) (v : V) (hv : v ∈ X) :
    ∃ a b : V, a ∈ X ∧ b ∈ X ∧ a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ X = {v, a, b} := by
  have h_erase : (X.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨a, b, hab, h_erase_eq⟩ := Finset.card_eq_two.mp h_erase
  have ha : a ∈ X.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_self a {b}
  have hb : b ∈ X.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha' : a ∈ X := Finset.mem_of_mem_erase ha
  have hb' : b ∈ X := Finset.mem_of_mem_erase hb
  have ha_ne : a ≠ v := Finset.ne_of_mem_erase ha
  have hb_ne : b ≠ v := Finset.ne_of_mem_erase hb
  refine ⟨a, b, ha', hb', ha_ne, hb_ne, hab, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxv : x = v
    · rw [hxv]; exact Finset.mem_insert_self v {a, b}
    · have hx_erase : x ∈ X.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
      rw [h_erase_eq] at hx_erase
      rcases Finset.mem_insert.mp hx_erase with rfl | hx_b
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self a {b})
      · rw [Finset.mem_singleton] at hx_b
        rw [hx_b]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hv
    · rcases Finset.mem_insert.mp hx' with rfl | hx''
      · exact ha'
      · rw [Finset.mem_singleton] at hx''; rw [hx'']; exact hb'

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: two_edges_cover_X_and_externals (Aristotle - slot326)
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_edges_cover_X_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) (hX_tri : X ∈ G.cliqueFinset 3) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (∃ u v, u ∈ X ∧ v ∈ X ∧ (e₁ = s(u,v) ∨ e₂ = s(u,v))) ∧
    (∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)) := by
  cases' universal_apex_exists G M hM hM_card hν X hX hX_card with h h;
  · simp +zetaDelta at *;
    rcases Finset.card_eq_three.mp hX_card with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use s(u, v), ?_, s(u, w), ?_ <;> simp_all +decide;
    · exact hX_tri.1 ( by aesop ) ( by aesop ) hu;
    · have := hX_tri.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  · rcases h with ( ⟨ v, hv, hv' ⟩ | ⟨ t, ht, ht' ⟩ );
    · obtain ⟨ a, b, ha, hb, hab, hv ⟩ := three_set_decomp X hX_card v hv;
      refine' ⟨ s(v, a), s(v, b), _, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.mem_edgeFinset ];
      · have := hX_tri.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        grind;
      · have := hX_tri.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        grind;
      · intro T hT; specialize hv' T hT; have := external_inter_card_two G M { v, a, b } hX ( by aesop ) T hT; simp_all +decide [ Finset.card_insert_of_notMem ] ;
        contrapose! this; aesop;
    · obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : V, a ∈ X ∧ b ∈ X ∧ c ∈ X ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ X = {a, b, c} := by
        rw [ Finset.card_eq_three ] at hX_card; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := hX_card; use a, b, c; aesop;
      by_cases h₁ : G.Adj a t <;> by_cases h₂ : G.Adj b c <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · refine' ⟨ s(a, t), _, s(b, c), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ];
        intro T hT; specialize ht' T hT; simp_all +decide [ isExternalOf ] ;
        rcases hT.2.2.1 with ⟨ u, v, huv, hu, hv, hu', hv' ⟩ ; aesop;
      · use s(b, c), by aesop, s(a, b), by aesop;
        simp_all +decide [ Sym2.eq_swap ];
        intro T hT; specialize ht' T hT; rcases hT with ⟨ hT₁, hT₂, hT₃, hT₄ ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
        rcases hT₃ with ⟨ u, v, huv, hu, hv, hu', hv' ⟩ ; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
        rcases hu' with ( rfl | rfl | rfl ) <;> rcases hv' with ( rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · have := hT₁.1 hu ht'; aesop;
        · have := hT₁.1 ( show t ∈ T from ht' ) ( show v ∈ T from hv ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: bridge_covered_by_selected_edges (SINGLE SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for bridge_covered_by_selected_edges:

A bridge B shares edges with at least 2 M-elements, say X and Y.
By bridge_covered_by_some_m_edge, ∃ edge from some M-element covering B.

KEY INSIGHT: The edge that covers B is the SHARED edge between B and that M-element.
When we select 2 edges for X using two_edges_cover_X_and_externals:
- At least one edge is FROM X (part of the guarantee)
- If B shares edge {u,v} with X where u or v is the "apex" vertex, then s(u,v) or
  a spoke from apex covers B

The critical observation:
- B shares edge {u,v} with X, meaning u,v ∈ X and u,v ∈ B
- Our 2-edge selection for X includes edges containing the apex
- In Case 2 (apex in X), apex can be u OR v (we have freedom to choose)
- By strategic apex selection, we can ensure B is covered

ALTERNATIVE APPROACH:
For any bridge B, consider ALL M-elements it shares edges with.
At least one of them will have an apex that lies on the shared edge,
meaning our edge selection covers B.
-/
lemma bridge_covered_by_selected_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3)
    (B : Finset V) (hB : isBridgeTriangle G M B) :
    ∃ X ∈ M, ∃ e₁ e₂ : Sym2 V,
      (∃ u v, u ∈ X ∧ v ∈ X ∧ (e₁ = s(u,v) ∨ e₂ = s(u,v))) ∧
      (∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)) ∧
      (e₁ ∈ B.sym2 ∨ e₂ ∈ B.sym2) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- FINAL TARGET: tau_le_8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

1. For each X ∈ M, use two_edges_cover_X_and_externals to get edge pair (e₁ˣ, e₂ˣ)
2. Let E = ⋃ₓ {e₁ˣ, e₂ˣ}. Then |E| ≤ 8.
3. By triangle_classification, every triangle T is:
   - M-element: covered by its own edge pair
   - External of some X: covered by X's edge pair (by two_edges_cover_X_and_externals)
   - Bridge: covered by bridge_covered_by_selected_edges
4. All edges in E are in G.edgeFinset (from two_edges_cover_X_and_externals)
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
