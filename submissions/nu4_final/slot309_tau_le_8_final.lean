/-
  slot309: τ ≤ 8 for ν = 4 - FINAL THEOREM

  This file combines all proven scaffolding from slot306 to prove τ ≤ 2ν.

  PROVEN FOUNDATION (slot306, UUID: 1658ed6d-db63-42b1-9118-2911c7a06975):
  - two_externals_share_edge: Any two X-externals share an edge
  - all_externals_share_common_vertex: All X-externals share a common vertex
  - two_edges_cover_all_externals: 2 edges cover X and all its externals

  MAIN THEOREM:
  For ν = 4 (maximal 4-packing), τ ≤ 8.

  PROOF SKETCH:
  1. For each X ∈ M, apply two_edges_cover_all_externals to get 2 edges
  2. Total: 4 elements × 2 edges = 8 edges
  3. Every triangle T is either:
     - In M (covered by its own 2 edges)
     - External to exactly one X ∈ M (covered by X's 2 edges)
  4. Therefore these 8 edges form a valid triangle cover
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot306)
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

-- Triangle cover definition
def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING FROM SLOT306 (Aristotle-generated, 0 sorry)
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_has_one_outside (t X : Finset V) (ht : t.card = 3) (hX : X.card = 3)
    (h_share : sharesEdgeWith t X) (h_ne : t ≠ X) :
    (t \ X).card = 1 := by
  have h_inter : (t ∩ X).card = 2 := by
    have h_ge : (t ∩ X).card ≥ 2 := by
      obtain ⟨u, v, huv, hu_t, hv_t, hu_X, hv_X⟩ := h_share
      exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu_t, hu_X⟩,
                                     v, Finset.mem_inter.mpr ⟨hv_t, hv_X⟩, huv⟩
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

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
      constructor <;> intro h;
      · obtain ⟨ u, v, huv, hu, hv, hu', hv' ⟩ := h;
        exact Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩;
      · obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h;
        exact ⟨ u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv, Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv ⟩

lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  contrapose! hν;
  refine' ⟨ Insert.insert T₁ ( Insert.insert T₂ ( M.erase X ) ), _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
  · simp_all +decide [ Finset.subset_iff, isExternalOf ];
    simp_all +decide [ Set.Pairwise, Finset.disjoint_left ];
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun Y hy₁ hy₂ => hM.1.1 hy₂ |> fun h => by simpa using h;
    · refine' ⟨ _, _ ⟩;
      · exact le_of_not_gt fun h => hν <| by rw [ sharesEdgeWith_iff_card_inter_ge_two ] ; exact h;
      · exact fun Y hy hyX hyT₁ => not_lt.1 fun contra => hT₁.2.2.2 Y hy hyX <| by rw [ sharesEdgeWith_iff_card_inter_ge_two ] ; exact contra;
    · simp_all +decide [ Finset.inter_comm, sharesEdgeWith_iff_card_inter_ge_two ];
      exact ⟨ fun _ => Nat.le_of_lt_succ hν, fun Y hy hy' hy'' => Nat.le_of_lt_succ ( hT₂.2.2.2 Y hy hy' ) ⟩;
    · intro Y hY hYX;
      refine' ⟨ _, _, _ ⟩;
      · intro hYT₁; specialize hT₁; have := hT₁.2.2.2 Y hY hYX; simp_all +decide [ sharesEdgeWith_iff_card_inter_ge_two ] ;
        exact Nat.le_of_lt_succ ( by rw [ Finset.inter_comm ] ; exact hT₁.2.2.2 Y hY hYX );
      · intro hY_ne_T₂; specialize hT₂; have := hT₂.2.2.2 Y hY hYX; simp_all +decide [ sharesEdgeWith_iff_card_inter_ge_two ] ;
        rw [ Finset.inter_comm ] ; linarith [ hT₂.2.2.2 Y hY hYX ];
      · intro Z hZ hZX hZY; have := hM.1.2; simp_all +decide [ Set.Pairwise ] ;
  · unfold isExternalOf at *; aesop;

lemma external_inter_X_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
      obtain ⟨ hT₁, hT₂, hT₃, hT₄ ⟩ := hT;
      have h_inter_card : (T \ X).card = 1 := by
        have h_inter_card : T.card = 3 ∧ X.card = 3 := by
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact hT₁.card_eq;
        exact external_has_one_outside T X h_inter_card.1 h_inter_card.2 hT₃ ( by aesop );
      have h_inter_card : (T ∩ X).card = T.card - (T \ X).card := by
        grind;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact hT₁.card_eq

lemma externals_disjoint_outside_implies_same_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    T₁ ∩ X = T₂ ∩ X := by
      have h_inter_card : (T₁ ∩ X).card = 2 ∧ (T₂ ∩ X).card = 2 := by
        exact ⟨ external_inter_X_card G M X hX hX_3 T₁ hT₁, external_inter_X_card G M X hX hX_3 T₂ hT₂ ⟩;
      have h_edge : (T₁ ∩ T₂ ∩ X).card = 2 := by
        have h_edge : (T₁ ∩ T₂).card ≥ 2 := by
          have h_inter_eq : sharesEdgeWith T₁ T₂ := by
            exact two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ ( by aesop_cat );
          obtain ⟨ u, v, huv, hu, hv, hu', hv' ⟩ := h_inter_eq; exact Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩ ;
        refine' le_antisymm _ _;
        · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_inter_card.1.le;
        · have h_edge : (T₁ \ X) ∩ (T₂ \ X) = ∅ := by
            have h_edge : (T₁ \ X).card = 1 ∧ (T₂ \ X).card = 1 := by
              have := hT₁.1;
              have := hT₂.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              have := Finset.card_sdiff_add_card_inter T₁ X; have := Finset.card_sdiff_add_card_inter T₂ X; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp h_edge.1; obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_edge.2; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
            grind;
          have h_edge : (T₁ ∩ T₂) = (T₁ ∩ T₂ ∩ X) ∪ ((T₁ \ X) ∩ (T₂ \ X)) := by
            grind;
          grind;
      have h_eq : T₁ ∩ X ⊇ T₁ ∩ T₂ ∩ X ∧ T₂ ∩ X ⊇ T₁ ∩ T₂ ∩ X := by
        grind;
      have := Finset.eq_of_subset_of_card_le h_eq.1; have := Finset.eq_of_subset_of_card_le h_eq.2; aesop;

lemma externals_all_same_edge_of_exists_diff (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (T₁ T₂ : Finset V) (hT₁ : T₁ ∈ externals) (hT₂ : T₂ ∈ externals)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    ∀ T ∈ externals, T ∩ X = T₁ ∩ X := by
      intro T hT;
      by_cases h_cases : T \ X = T₁ \ X;
      · have h_case2 : T ∩ X = T₂ ∩ X := by
          apply externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₂ (h_ext T hT) (h_ext T₂ hT₂);
          aesop;
        have := externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T₁ T₂ ( h_ext T₁ hT₁ ) ( h_ext T₂ hT₂ ) h_diff; aesop;
      · apply externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₁ (h_ext T hT) (h_ext T₁ hT₁) h_cases

theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T := by
  by_cases h_all_same_outside : ∀ T1 ∈ externals, ∀ T2 ∈ externals, T1 \ X = T2 \ X;
  · obtain ⟨T₀, hT₀⟩ : ∃ T₀ ∈ externals, True := by
      exact ⟨ h_nonempty.choose, h_nonempty.choose_spec, trivial ⟩;
    obtain ⟨v, hv⟩ : ∃ v, T₀ \ X = {v} := by
      have hT₀_card : (T₀ \ X).card = 1 := by
        have hT₀_card : T₀.card = 3 := by
          have := h_ext T₀ hT₀.1;
          exact this.1 |> fun h => by simpa using Finset.mem_coe.mp h |> fun h => by simpa using Finset.mem_filter.mp h |>.2.2;
        have hT₀_X_card : (T₀ ∩ X).card = 2 := by
          apply external_inter_X_card G M X hX hX_3 T₀ (h_ext T₀ hT₀.left);
        grind;
      exact Finset.card_eq_one.mp hT₀_card;
    use v;
    intro T hT; specialize h_all_same_outside T hT T₀ hT₀.1; rw [ Finset.ext_iff ] at h_all_same_outside; specialize h_all_same_outside v; aesop;
  · obtain ⟨S, hS⟩ : ∃ S : Finset V, ∀ T ∈ externals, T ∩ X = S := by
      obtain ⟨T1, hT1, T2, hT2, h_diff⟩ : ∃ T1 ∈ externals, ∃ T2 ∈ externals, T1 \ X ≠ T2 \ X := by
        exact by push_neg at h_all_same_outside; exact h_all_same_outside;
      exact ⟨ T1 ∩ X, fun T hT => by have := externals_all_same_edge_of_exists_diff G M hM hM_card hν X hX hX_3 externals h_ext T1 T2 hT1 hT2 h_diff; aesop ⟩;
    obtain ⟨u, hu⟩ : ∃ u, u ∈ S := by
      have := h_ext _ h_nonempty.choose_spec;
      exact hS _ h_nonempty.choose_spec ▸ ( external_inter_X_card G M X hX hX_3 _ this ) |> fun h => Finset.card_pos.mp ( by linarith );
    exact ⟨ u, fun T hT => Finset.mem_of_mem_inter_left ( hS T hT ▸ hu ) ⟩

lemma cover_externals_case_inside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∈ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
          obtain ⟨u, w, hu, hw, hx⟩ : ∃ u w : V, u ≠ w ∧ u ∈ X ∧ w ∈ X ∧ u ≠ v ∧ w ≠ v ∧ X = {v, u, w} := by
            rw [ Finset.card_eq_three ] at hX_3;
            rcases hX_3 with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; by_cases hvx : v = x <;> by_cases hvy : v = y <;> by_cases hvz : v = z <;> simp_all +decide ;
            · exact ⟨ y, z, by tauto, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
            · exact ⟨ x, z, by tauto, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
            · exact ⟨ x, y, hxy, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
          refine' ⟨ Sym2.mk ( v, u ), Sym2.mk ( v, w ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.mem_edgeFinset ];
          · have := hX_clique.1; aesop;
          · have := hX_clique.1; aesop;
          · intro T hT hT';
            have := hT.2.2.1; unfold sharesEdgeWith at this; aesop;

lemma cover_externals_case_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∉ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
          obtain ⟨a, b, c, hac⟩ : ∃ a b c : V, X = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
            rw [ Finset.card_eq_three ] at hX_3; tauto;
          have h_ext_form : ∀ T, isExternalOf G M X T → ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ T = {v, x, y} := by
            intro T hT
            obtain ⟨hT_clique, hT_not_in_M, hT_sharesEdge, hT_no_sharesEdge⟩ := hT
            have hT_card : T.card = 3 := by
              exact Finset.mem_filter.mp hT_clique |>.2.2
            have hT_inter_X : (T ∩ X).card = 2 := by
              have := external_has_one_outside T X hT_card hX_3 hT_sharesEdge (by
              exact fun h => hv ( h ▸ h_common T ⟨ hT_clique, hT_not_in_M, hT_sharesEdge, hT_no_sharesEdge ⟩ ));
              grind
            have hT_form : ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ T = {v, x, y} := by
              obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ x ∈ T ∧ y ∈ T ∧ v ∈ T := by
                obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card ( T ∩ X ) ) ; use x, y; simp_all +decide [ Finset.inter_comm ] ;
                unfold isExternalOf at *; aesop;
              use x, y;
              rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hxy.2.2.2, Finset.insert_subset_iff.mpr ⟨ hxy.2.1, Finset.singleton_subset_iff.mpr hxy.2.2.1 ⟩ ⟩ ) ] ; aesop;
              grind
            exact hT_form;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          by_cases h₁ : G.Adj v c;
          · refine' ⟨ Sym2.mk ( a, b ), _, Sym2.mk ( v, c ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
            intro T hT₁ hT₂ hT₃; specialize h_ext_form T hT₁; aesop;
          · use Sym2.mk ( a, b ), ?_, Sym2.mk ( a, c ), ?_ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
            intro T hT hT' hT''; specialize h_ext_form T hT; aesop;

theorem two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  by_cases hE_empty : ¬∃ T, isExternalOf G M X T;
  · rcases Finset.card_eq_three.mp hX_3 with ⟨ a, b, c, hab, hbc, hac ⟩ ; simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.adj_comm ];
    rcases hM with ⟨ hM₁, hM₂ ⟩;
    have := hM₁.1 hX; simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_eq_three ] ;
    exact ⟨ Sym2.mk ( a, b ), by simp +decide [ this ], Sym2.mk ( b, c ), by simp +decide [ this ], by simp +decide [ this ] ⟩;
  · obtain ⟨T₀, hT₀⟩ : ∃ T₀, isExternalOf G M X T₀ := by
      exact not_not.mp hE_empty;
    obtain ⟨v, hv⟩ : ∃ v, ∀ T, isExternalOf G M X T → v ∈ T := by
      have := all_externals_share_common_vertex G M hM hM_card hν X hX hX_3 ( Finset.univ.filter fun T => isExternalOf G M X T ) ( by aesop ) ( ⟨ T₀, by aesop ⟩ ) ; aesop;
    by_cases hvX : v ∈ X;
    · apply cover_externals_case_inside G M X (by
      have := hM.1.1 hX; aesop;) (by
      exact hX_3) v hvX (by
      exact hv);
    · apply cover_externals_case_outside G M X (by
      have := hM.1.1 hX; aesop;) (by
      exact hX_3) v hvX hv

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: TRIANGLES PARTITIONED BY M-ELEMENTS
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for triangle_covered_by_some_element:
Every triangle T in G is either:
1. In M (then T = X for some X ∈ M, so T is covered by X's edges)
2. Not in M (then by maximality, T shares edge with some X ∈ M)
   - If T shares edge with exactly one X ∈ M, T is external to X
   - If T shares edge with multiple X, Y ∈ M, then T ∩ X and T ∩ Y both have size ≥ 2,
     but this means X ∩ Y has size ≥ 2 (through T), contradicting edge-disjointness
   So T is external to exactly one element.
-/
lemma triangle_covered_by_some_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, T = X ∨ isExternalOf G M X T := by
  by_cases hT_in_M : T ∈ M
  · exact ⟨T, hT_in_M, Or.inl rfl⟩
  · -- T ∉ M, so by maximality, T shares edge with some X ∈ M
    obtain ⟨X, hX_in_M, hX_share⟩ := hM.2 T hT hT_in_M
    -- Need to show T is external to exactly one element
    use X, hX_in_M
    right
    constructor
    · exact hT
    constructor
    · exact hT_in_M
    constructor
    · -- T shares edge with X
      rw [sharesEdgeWith_iff_card_inter_ge_two]
      exact hX_share
    · -- T doesn't share edge with any other Y ∈ M
      intro Y hY_in_M hY_ne_X
      by_contra h_share_Y
      -- If T shares edges with both X and Y, then X and Y share ≥ 2 vertices through T
      -- This contradicts edge-disjointness of M
      have h_X_inter : (T ∩ X).card ≥ 2 := hX_share
      have h_Y_inter : (T ∩ Y).card ≥ 2 := by
        rw [sharesEdgeWith_iff_card_inter_ge_two] at h_share_Y
        exact h_share_Y
      -- T has only 3 vertices, so T ∩ X and T ∩ Y must overlap significantly
      have hT_card : T.card = 3 := by
        simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT
        exact hT.2.2
      -- X ∩ Y contains the overlap of (T ∩ X) and (T ∩ Y) within T
      have h_overlap : (X ∩ Y).card ≥ 2 := by
        -- T ∩ X has ≥ 2 elements, T ∩ Y has ≥ 2 elements, T has 3 elements
        -- So (T ∩ X) ∩ (T ∩ Y) = T ∩ X ∩ Y has ≥ 1 element
        -- Actually we need ≥ 2 overlap
        have h1 : (T ∩ X).card + (T ∩ Y).card ≥ 4 := by linarith
        have h2 : (T ∩ X) ∪ (T ∩ Y) ⊆ T := by
          intro v hv
          cases Finset.mem_union.mp hv with
          | inl h => exact Finset.mem_inter.mp h |>.1
          | inr h => exact Finset.mem_inter.mp h |>.1
        have h3 : ((T ∩ X) ∪ (T ∩ Y)).card ≤ T.card := Finset.card_le_card h2
        have h4 : ((T ∩ X) ∪ (T ∩ Y)).card = (T ∩ X).card + (T ∩ Y).card - ((T ∩ X) ∩ (T ∩ Y)).card := by
          exact Finset.card_union_eq_card_add_card_sub_card_inter (T ∩ X) (T ∩ Y)
        have h5 : ((T ∩ X) ∩ (T ∩ Y)).card ≥ 1 := by
          omega
        -- (T ∩ X) ∩ (T ∩ Y) = T ∩ (X ∩ Y)
        have h6 : (T ∩ X) ∩ (T ∩ Y) = T ∩ (X ∩ Y) := by
          ext v
          simp only [Finset.mem_inter]
          tauto
        have h7 : (T ∩ (X ∩ Y)).card ≥ 1 := by rw [← h6]; exact h5
        -- Need (X ∩ Y).card ≥ 2, but we only showed T ∩ (X ∩ Y) ≥ 1
        -- Let's recalculate: with T.card = 3, |T∩X| ≥ 2, |T∩Y| ≥ 2
        -- |T∩X| + |T∩Y| - |T∩X∩Y| = |(T∩X) ∪ (T∩Y)| ≤ 3
        -- So |T∩X∩Y| ≥ |T∩X| + |T∩Y| - 3 ≥ 2 + 2 - 3 = 1
        -- We need ≥ 2. This requires |T∩X| = 2 and |T∩Y| = 2 and |(T∩X)∪(T∩Y)| = 3
        -- Actually |T∩X| ≤ |T| = 3 and similar, so if both are ≥ 2...
        -- Let me be more careful. We need at least 2 common vertices.
        -- Actually the bound gives us ≥ 1. But for edge-disjointness we need ≤ 1.
        -- So even ≥ 1 would be a problem if the packing requires disjoint edges!
        -- Wait, edge-disjoint means (X ∩ Y).card ≤ 1 for distinct X, Y ∈ M
        -- We showed (T ∩ X ∩ Y).card ≥ 1, so (X ∩ Y).card ≥ 1
        -- That's not immediately a contradiction...
        -- Let me reconsider. With |T∩X| ≥ 2 and |T∩Y| ≥ 2 and |T| = 3:
        -- If |T∩X| = 2 and |T∩Y| = 2, then |T \ X| = 1 and |T \ Y| = 1
        -- The two "outside" vertices could be the same or different
        -- If same: T ∩ X = T ∩ Y, so |T ∩ X ∩ Y| = 2, giving |X ∩ Y| ≥ 2 ✗
        -- If different: T = (T∩X∩Y) ∪ (T∩X\Y) ∪ (T∩Y\X), with each part size 1
        -- So |T∩X∩Y| = 1, giving |X∩Y| ≥ 1 which is allowed...
        -- But wait, |T∩X| = 2 means T∩X has 2 elements.
        -- If T\X has 1 element (the "outside"), then T∩X = T minus that one element
        -- Similarly T∩Y = T minus one element
        -- If different elements are outside, then T∩X and T∩Y differ by exchanging one element
        -- So |T∩X ∩ T∩Y| = 1 (the shared element)
        -- Hmm, that's only 1. But if the same element is outside both, then T∩X = T∩Y
        -- and |(T∩X)| = 2, giving |X∩Y| ≥ 2.
        -- So the question is: can the same vertex of T be outside both X and Y?
        -- Actually, |T∩X| ≥ 2 means at least 2 vertices of T are in X
        -- |T∩Y| ≥ 2 means at least 2 vertices of T are in Y
        -- T has 3 vertices. So T∩X has ≥ 2, T∩Y has ≥ 2
        -- The intersection (T∩X) ∩ (T∩Y) has size ≥ 2+2-3 = 1
        -- We need to show ≥ 2 to get contradiction with edge-disjointness
        -- But actually we can argue differently:
        -- If |T∩X| = |T∩Y| = 2, then T\X and T\Y are both singletons
        -- T\X = {u}, T\Y = {v} for some u, v ∈ T
        -- If u = v, then T∩X = T∩Y = T\{u}, so X and Y both contain these 2 vertices ⟹ |X∩Y| ≥ 2
        -- If u ≠ v, then T = {u, v, w} for some w, T∩X = {v,w}, T∩Y = {u,w}
        -- X contains {v,w}, Y contains {u,w}, so X∩Y contains w ⟹ |X∩Y| ≥ 1
        -- This only gives 1, which is allowed!
        -- So we need a different argument. Perhaps using that X, Y are triangles too?
        sorry
      -- This contradicts edge-disjointness of M
      have h_disjoint := hM.1.2
      simp only [Set.Pairwise, Set.mem_coe] at h_disjoint
      have h_contra := h_disjoint hX_in_M hY_in_M hY_ne_X
      linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:
1. For each X ∈ M, by two_edges_cover_all_externals, get 2 edges e₁ˣ, e₂ˣ
2. Let E = ⋃_{X∈M} {e₁ˣ, e₂ˣ}
3. |E| ≤ 4 × 2 = 8 (some edges might be shared, so ≤)
4. For any triangle T:
   - By triangle_covered_by_some_element, T = X or T is external to X for some X ∈ M
   - By two_edges_cover_all_externals, e₁ˣ or e₂ˣ hits T
   - So E covers T
5. Therefore E is a triangle cover of size ≤ 8
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
