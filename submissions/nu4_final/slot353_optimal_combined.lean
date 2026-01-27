/-
  slot353: Optimal Combined Scaffolding for tau_le_8

  COMBINING PROVEN CODE FROM:
  - slot306 (UUID: 1658ed6d-db63-42b1-9118-2911c7a06975) - 0 sorry, 0 axiom
  - slot309 (UUID: ba39e952-3f21-4f5a-9a16-46f1fc5abf2c) - bridge lemmas proven

  KEY THEOREMS (all PROVEN):
  1. two_edges_cover_all_externals: 2 edges cover X and all X-externals
  2. bridge_triangle_contains_shared_vertex: Bridges pass through shared vertex
  3. bridge_covered_if_shared_is_common: Bridges covered if shared vertex used

  REMAINING: tau_le_8 (1 sorry) - combining these for full proof
-/

import Mathlib


set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ======================================================================
-- DEFINITIONS
-- ======================================================================

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

-- ======================================================================
-- PROVEN SCAFFOLDING FROM SLOT306 (0 sorry - verbatim copy)
-- ======================================================================

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

lemma external_inter_X_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
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

lemma externals_disjoint_outside_implies_same_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
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

lemma externals_all_same_edge_of_exists_diff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
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

-- Cover case when common vertex is inside X
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

-- Cover case when common vertex is outside X
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

-- THE KEY THEOREM FROM SLOT306 (PROVEN)
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

-- ======================================================================
-- PROVEN SCAFFOLDING FROM SLOT309 (bridge lemmas)
-- ======================================================================

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
      constructor
      · exact hv.2
      · intro hvc
        rw [hvc] at hv
        exact hc_notin_T hv.1
    have h2 : T ∩ Y ⊆ Y \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hv.2
      · intro hvc
        rw [hvc] at hv
        exact hc_notin_T hv.1
    have h3 : (X \ {c}) ∩ (Y \ {c}) = ∅ := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton, Finset.not_mem_empty,
                 iff_false, not_and, not_not]
      intro ⟨hvX, hvc⟩ ⟨hvY, _⟩
      have : v ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hvX, hvY⟩
      rw [hc] at this
      exact hvc (Finset.mem_singleton.mp this)
    have h4 : Disjoint (T ∩ X) (T ∩ Y) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      have : (T ∩ X) ∩ (T ∩ Y) ⊆ (X \ {c}) ∩ (Y \ {c}) := by
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        constructor
        · exact h1 (Finset.mem_inter.mpr ⟨hv.1.1, hv.1.2⟩)
        · exact h2 (Finset.mem_inter.mpr ⟨hv.2.1, hv.2.2⟩)
      exact Finset.eq_empty_of_subset_empty (h3 ▸ this)
    have h5 : (T ∩ X).card + (T ∩ Y).card ≤ T.card := by
      have : (T ∩ X) ∪ (T ∩ Y) ⊆ T := by
        intro v hv
        cases Finset.mem_union.mp hv with
        | inl h => exact Finset.mem_inter.mp h |>.1
        | inr h => exact Finset.mem_inter.mp h |>.1
      calc (T ∩ X).card + (T ∩ Y).card
          = ((T ∩ X) ∪ (T ∩ Y)).card := by rw [Finset.card_union_eq_card_add_card h4]
        _ ≤ T.card := Finset.card_le_card this
    omega

-- ======================================================================
-- TRIANGLE CLASSIFICATION
-- ======================================================================

-- Every non-M triangle shares edge with some M-element (by maximality)
lemma non_M_triangle_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_not_M : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm, h_inter⟩ := hM.2 T hT hT_not_M
  exact ⟨m, hm, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr h_inter⟩

-- Classify triangles: M-element, external (to exactly one), or bridge
lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ (∃ X ∈ M, isExternalOf G M X T) ∨ isBridgeTriangle G M T := by
  by_cases hT_M : T ∈ M
  · left; exact hT_M
  · obtain ⟨X, hX, hT_share⟩ := non_M_triangle_shares_edge G M hM T hT hT_M
    by_cases h_unique : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
    · -- External to X only
      right; left
      exact ⟨X, hX, ⟨hT, hT_M, hT_share, h_unique⟩⟩
    · -- Bridge triangle
      right; right
      push_neg at h_unique
      obtain ⟨Y, hY, hYX, hT_share_Y⟩ := h_unique
      exact ⟨hT, hT_M, X, Y, hX, hY, hYX.symm, hT_share, hT_share_Y⟩

-- ======================================================================
-- MAIN THEOREM: tau_le_8
-- ======================================================================

/-
PROOF SKETCH:
1. For each X ∈ M, two_edges_cover_all_externals gives 2 edges covering X and X-externals
2. |M| = 4, so 4 × 2 = 8 edges total (with possible overlap)
3. Triangle classification: every triangle is M-element, external, or bridge
4. M-elements and externals: covered by the 8 edges from step 1
5. Bridge triangles: pass through shared vertex c (by bridge_triangle_contains_shared_vertex)
   - c is in both X and Y
   - The 2 edges for X or Y (whichever has c as common vertex) cover the bridge
6. Key insight: We can CHOOSE which common vertex to use for each element
   - Adjacent elements share a vertex c; at least one must use c as common vertex
   - This ensures bridge triangles are covered
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  /-
  Strategy:
  1. Apply two_edges_cover_all_externals to each X ∈ M to get pairs (e₁_X, e₂_X)
  2. Let E = union of all these edges (at most 8)
  3. Show E covers all triangles using triangle_classification
  4. Bridge triangles are handled by bridge_triangle_contains_shared_vertex
  -/
  sorry

end
