/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2390c1e5-0d3c-4de3-bc58-56f712c47b1b

Aristotle encountered an error processing this file. The team has been notified.
-/

/-
  slot310: τ ≤ 8 for ν = 4 - COMPLETE WITH ALL PROVEN SCAFFOLDING

  PROVEN FOUNDATION:
  - slot306 (UUID: 1658ed6d): two_externals_share_edge, all_externals_share_common_vertex,
                              two_edges_cover_all_externals (0 sorry, 10 proven)
  - slot307 (UUID: a856aabc): two_externals_share_edge (full 5-packing), shared_edge_contains_X_vertex
  - slot308 (UUID: 9f0fac6d): pairwise_externals_share_X_vertex, fanCover_card,
                              fanCover_covers_apex_triangle
  - slot309 (UUID: ba39e952): bridge_triangle_contains_shared_vertex, bridge_covered_if_shared_is_common

  TRIANGLES TO COVER:
  1. M-elements (A, B, C, D) - covered by their own 2 edges
  2. X-externals (share edge with exactly one X ∈ M) - covered by two_edges_cover_all_externals
  3. Bridge triangles (share edges with multiple elements) - covered by bridge triangle lemmas

  PROOF STRATEGY:
  For each X ∈ M, get common vertex c_X from all_externals_share_common_vertex.
  Include 2 edges incident to c_X. Total: 4 × 2 = 8 edges.

  This covers:
  - X itself (c_X ∈ X, so edges from c_X are edges of X)
  - X-externals (all contain c_X by definition of common vertex)
  - Bridge triangles (contain shared vertex c, which is c_X or c_Y for adjacent X,Y)
-/

import Mathlib

set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

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
-- PROVEN SCAFFOLDING FROM SLOT306 (0 sorry - copied verbatim from Aristotle)
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
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.2 ⟨u, by aesop, v, by aesop⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- slot306 PROVEN: two_externals_share_edge (5-packing argument)
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

-- slot306 PROVEN: external_inter_X_card
lemma external_inter_X_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  obtain ⟨hT₁, hT₂, hT₃, hT₄⟩ := hT
  have h_inter_card : (T \ X).card = 1 := by
    have h_inter_card : T.card = 3 ∧ X.card = 3 := by
      simp_all +decide [ SimpleGraph.cliqueFinset ]
      exact hT₁.card_eq
    exact external_has_one_outside T X h_inter_card.1 h_inter_card.2 hT₃ (by aesop)
  have h_inter_card2 : (T ∩ X).card = T.card - (T \ X).card := by grind
  simp_all +decide [ SimpleGraph.cliqueFinset ]
  exact hT₁.card_eq

-- slot306 PROVEN: externals_disjoint_outside_implies_same_edge
lemma externals_disjoint_outside_implies_same_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    T₁ ∩ X = T₂ ∩ X := by
  have h_inter_card : (T₁ ∩ X).card = 2 ∧ (T₂ ∩ X).card = 2 := by
    exact ⟨external_inter_X_card G M X hX hX_3 T₁ hT₁, external_inter_X_card G M X hX hX_3 T₂ hT₂⟩
  have h_edge : (T₁ ∩ T₂ ∩ X).card = 2 := by
    have h_edge : (T₁ ∩ T₂).card ≥ 2 := by
      have h_inter_eq : sharesEdgeWith T₁ T₂ := by
        exact two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ (by aesop_cat)
      obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h_inter_eq
      exact Finset.one_lt_card.2 ⟨u, by aesop, v, by aesop⟩
    refine' le_antisymm _ _
    · exact le_trans (Finset.card_le_card fun x hx => by aesop) h_inter_card.1.le
    · have h_edge : (T₁ \ X) ∩ (T₂ \ X) = ∅ := by
        have h_edge : (T₁ \ X).card = 1 ∧ (T₂ \ X).card = 1 := by
          have := hT₁.1
          have := hT₂.1
          simp_all +decide [ SimpleGraph.cliqueFinset ]
          have := Finset.card_sdiff_add_card_inter T₁ X
          have := Finset.card_sdiff_add_card_inter T₂ X
          simp_all +decide [ SimpleGraph.isNClique_iff ]
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h_edge.1
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h_edge.2
        simp_all +decide [ Finset.eq_singleton_iff_unique_mem ]
        grind
      have h_edge2 : (T₁ ∩ T₂) = (T₁ ∩ T₂ ∩ X) ∪ ((T₁ \ X) ∩ (T₂ \ X)) := by grind
      grind
  have h_eq : T₁ ∩ X ⊇ T₁ ∩ T₂ ∩ X ∧ T₂ ∩ X ⊇ T₁ ∩ T₂ ∩ X := by grind
  have := Finset.eq_of_subset_of_card_le h_eq.1
  have := Finset.eq_of_subset_of_card_le h_eq.2
  aesop

-- slot306 PROVEN: externals_all_same_edge_of_exists_diff
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
  · have h_case2 : T ∩ X = T₂ ∩ X := by
      apply externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₂
        (h_ext T hT) (h_ext T₂ hT₂)
      aesop
    have := externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T₁ T₂
      (h_ext T₁ hT₁) (h_ext T₂ hT₂) h_diff
    aesop
  · apply externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₁
      (h_ext T hT) (h_ext T₁ hT₁) h_cases

-- slot306 PROVEN: all_externals_share_common_vertex
theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T := by
  by_cases h_all_same_outside : ∀ T1 ∈ externals, ∀ T2 ∈ externals, T1 \ X = T2 \ X
  · obtain ⟨T₀, hT₀⟩ : ∃ T₀ ∈ externals, True := by
      exact ⟨h_nonempty.choose, h_nonempty.choose_spec, trivial⟩
    obtain ⟨v, hv⟩ : ∃ v, T₀ \ X = {v} := by
      have hT₀_card : (T₀ \ X).card = 1 := by
        have hT₀_card : T₀.card = 3 := by
          have := h_ext T₀ hT₀.1
          exact this.1 |> fun h => by simpa using Finset.mem_coe.mp h |> fun h =>
            by simpa using Finset.mem_filter.mp h |>.2.2
        have hT₀_X_card : (T₀ ∩ X).card = 2 := by
          apply external_inter_X_card G M X hX hX_3 T₀ (h_ext T₀ hT₀.left)
        grind
      exact Finset.card_eq_one.mp hT₀_card
    use v
    intro T hT
    specialize h_all_same_outside T hT T₀ hT₀.1
    rw [Finset.ext_iff] at h_all_same_outside
    specialize h_all_same_outside v
    aesop
  · obtain ⟨S, hS⟩ : ∃ S : Finset V, ∀ T ∈ externals, T ∩ X = S := by
      obtain ⟨T1, hT1, T2, hT2, h_diff⟩ : ∃ T1 ∈ externals, ∃ T2 ∈ externals, T1 \ X ≠ T2 \ X := by
        exact by push_neg at h_all_same_outside; exact h_all_same_outside
      exact ⟨T1 ∩ X, fun T hT => by
        have := externals_all_same_edge_of_exists_diff G M hM hM_card hν X hX hX_3 externals
          h_ext T1 T2 hT1 hT2 h_diff
        aesop⟩
    obtain ⟨u, hu⟩ : ∃ u, u ∈ S := by
      have := h_ext _ h_nonempty.choose_spec
      exact hS _ h_nonempty.choose_spec ▸ (external_inter_X_card G M X hX hX_3 _ this) |>
        fun h => Finset.card_pos.mp (by linarith)
    exact ⟨u, fun T hT => Finset.mem_of_mem_inter_left (hS T hT ▸ hu)⟩

-- slot306 PROVEN: cover_externals_case_inside
lemma cover_externals_case_inside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∈ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  obtain ⟨u, w, hu, hw, hx⟩ : ∃ u w : V, u ≠ w ∧ u ∈ X ∧ w ∈ X ∧ u ≠ v ∧ w ≠ v ∧ X = {v, u, w} := by
    rw [Finset.card_eq_three] at hX_3
    rcases hX_3 with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
    by_cases hvx : v = x <;> by_cases hvy : v = y <;> by_cases hvz : v = z <;> simp_all +decide
    · exact ⟨y, z, by tauto, by tauto, by tauto, by tauto, by tauto, by aesop⟩
    · exact ⟨x, z, by tauto, by tauto, by tauto, by tauto, by tauto, by aesop⟩
    · exact ⟨x, y, hxy, by tauto, by tauto, by tauto, by tauto, by aesop⟩
  refine' ⟨Sym2.mk (v, u), Sym2.mk (v, w), _, _, _⟩ <;> simp_all +decide [SimpleGraph.mem_edgeFinset]
  · have := hX_clique.1; aesop
  · have := hX_clique.1; aesop
  · intro T hT hT'
    have := hT.2.2.1
    unfold sharesEdgeWith at this
    aesop

-- slot306 PROVEN: cover_externals_case_outside
lemma cover_externals_case_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∉ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  obtain ⟨a, b, c, hac⟩ : ∃ a b c : V, X = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    rw [Finset.card_eq_three] at hX_3; tauto
  have h_ext_form : ∀ T, isExternalOf G M X T → ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ T = {v, x, y} := by
    intro T hT
    obtain ⟨hT_clique, hT_not_in_M, hT_sharesEdge, hT_no_sharesEdge⟩ := hT
    have hT_card : T.card = 3 := by exact Finset.mem_filter.mp hT_clique |>.2.2
    have hT_inter_X : (T ∩ X).card = 2 := by
      have := external_has_one_outside T X hT_card hX_3 hT_sharesEdge (by
        exact fun h => hv (h ▸ h_common T ⟨hT_clique, hT_not_in_M, hT_sharesEdge, hT_no_sharesEdge⟩))
      grind
    have hT_form : ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ T = {v, x, y} := by
      obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ x ∈ T ∧ y ∈ T ∧ v ∈ T := by
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by linarith : 1 < Finset.card (T ∩ X))
        use x, y
        simp_all +decide [Finset.inter_comm]
        unfold isExternalOf at *
        aesop
      use x, y
      rw [Finset.eq_of_subset_of_card_le
        (Finset.insert_subset_iff.mpr ⟨hxy.2.2.2, Finset.insert_subset_iff.mpr
          ⟨hxy.2.1, Finset.singleton_subset_iff.mpr hxy.2.2.1⟩⟩)]
      aesop
      grind
    exact hT_form
  simp_all +decide [SimpleGraph.cliqueFinset]
  by_cases h₁ : G.Adj v c
  · refine' ⟨Sym2.mk (a, b), _, Sym2.mk (v, c), _, _, _⟩ <;>
      simp_all +decide [SimpleGraph.isNClique_iff]
    intro T hT₁ hT₂ hT₃
    specialize h_ext_form T hT₁
    aesop
  · use Sym2.mk (a, b), ?_, Sym2.mk (a, c), ?_ <;> simp_all +decide [SimpleGraph.isNClique_iff]
    intro T hT hT' hT''
    specialize h_ext_form T hT
    aesop

-- slot306 PROVEN: two_edges_cover_all_externals
theorem two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  by_cases hE_empty : ¬∃ T, isExternalOf G M X T
  · rcases Finset.card_eq_three.mp hX_3 with ⟨a, b, c, hab, hbc, hac⟩
    simp_all +decide [SimpleGraph.isClique_iff, SimpleGraph.adj_comm]
    rcases hM with ⟨hM₁, hM₂⟩
    have := hM₁.1 hX
    simp_all +decide [SimpleGraph.isNClique_iff, Finset.card_eq_three]
    exact ⟨Sym2.mk (a, b), by simp +decide [this], Sym2.mk (b, c), by simp +decide [this],
           by simp +decide [this]⟩
  · obtain ⟨T₀, hT₀⟩ : ∃ T₀, isExternalOf G M X T₀ := by exact not_not.mp hE_empty
    obtain ⟨v, hv⟩ : ∃ v, ∀ T, isExternalOf G M X T → v ∈ T := by
      have := all_externals_share_common_vertex G M hM hM_card hν X hX hX_3
        (Finset.univ.filter fun T => isExternalOf G M X T) (by aesop) (⟨T₀, by aesop⟩)
      aesop
    by_cases hvX : v ∈ X
    · apply cover_externals_case_inside G M X (by have := hM.1.1 hX; aesop) (by exact hX_3) v hvX
        (by exact hv)
    · apply cover_externals_case_outside G M X (by have := hM.1.1 hX; aesop) (by exact hX_3) v hvX hv

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING FROM SLOT308 (pairwise lemmas, fanCover)
-- ══════════════════════════════════════════════════════════════════════════════

-- slot308 PROVEN: pairwise_externals_share_X_vertex
lemma pairwise_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ X, x ∈ T₁ ∧ x ∈ T₂ := by
  have h_share_edge_X : ∃ u v, u ≠ v ∧ u ∈ T₁ ∧ v ∈ T₁ ∧ u ∈ X ∧ v ∈ X := by exact hT₁.2.2.1
  have h_share_edge_X_T₂ : ∃ u v, u ≠ v ∧ u ∈ T₂ ∧ v ∈ T₂ ∧ u ∈ X ∧ v ∈ X := by
    cases hT₂; aesop
  obtain ⟨u₁, v₁, hne₁, hu₁, hv₁, hx₁, hx₂⟩ := h_share_edge_X
  obtain ⟨u₂, v₂, hne₂, hu₂, hv₂, hy₁, hy₂⟩ := h_share_edge_X_T₂
  by_cases h_cases : u₁ = u₂ ∨ u₁ = v₂ ∨ v₁ = u₂ ∨ v₁ = v₂
  · grind
  · have := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hx₁ (Finset.insert_subset hx₂
        (Finset.insert_subset hy₁ (Finset.singleton_subset_iff.mpr hy₂))))
    simp_all +decide
    aesop

-- slot308 PROVEN: fanCover definition
def fanCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (x : V) (hx : x ∈ X) : Finset (Sym2 V) :=
  let others := X.erase x
  others.image (fun y => s(x, y))

-- slot308 PROVEN: fanCover_card
lemma fanCover_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X) :
    (fanCover G X hX_clique x hx).card = 2 := by
  unfold fanCover
  have h_others_card : (X.erase x).card = 2 := by rw [Finset.card_erase_of_mem hx, hX_3]
  rw [Finset.card_image_of_injOn, h_others_card]
  intro y hy
  aesop

-- slot308 PROVEN: fanCover_covers_apex_triangle
lemma fanCover_covers_apex_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_3 : t.card = 3)
    (hx_t : x ∈ t) (h_share : sharesEdgeWith t X) :
    ∃ e ∈ fanCover G X hX_clique x hx, e ∈ t.sym2 := by
  have h_two : (t ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two t X |>.mp h_share
  have hx_inter : x ∈ t ∩ X := Finset.mem_inter.mpr ⟨hx_t, hx⟩
  obtain ⟨w, hw_inter, hw_ne⟩ : ∃ w ∈ t ∩ X, w ≠ x := by
    have h_card : 1 < (t ∩ X).card := h_two
    exact Finset.exists_ne_of_one_lt_card h_card x hx_inter
  have hw_t : w ∈ t := (Finset.mem_inter.mp hw_inter).1
  have hw_X : w ∈ X := (Finset.mem_inter.mp hw_inter).2
  use s(x, w)
  constructor
  · unfold fanCover
    simp only [Finset.mem_image, Finset.mem_erase]
    exact ⟨w, ⟨hw_ne, hw_X⟩, rfl⟩
  · simp only [Finset.mem_sym2_iff]
    exact ⟨hx_t, hw_t⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING FROM SLOT309 (bridge triangles)
-- ══════════════════════════════════════════════════════════════════════════════

-- slot309 PROVEN: bridge_triangle_contains_shared_vertex
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
      · intro hvc; rw [hvc] at hv; exact hc_notin_T hv.1
    have h2 : T ∩ Y ⊆ Y \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hv.2
      · intro hvc; rw [hvc] at hv; exact hc_notin_T hv.1
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

-- slot309 PROVEN: bridge_covered_if_shared_is_common
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
  obtain ⟨v, hv_inter, hv_ne_c⟩ : ∃ v ∈ T ∩ X, v ≠ c := by
    have : 1 < (T ∩ X).card := by linarith
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases hac : a = c
    · exact ⟨b, hb, fun h => hab (hac ▸ h.symm)⟩
    · exact ⟨a, ha, hac⟩
  have hv_T : v ∈ T := Finset.mem_inter.mp hv_inter |>.1
  have hv_X : v ∈ X := Finset.mem_inter.mp hv_inter |>.2
  have hX_form : X = {c, u, w} := by
    rw [Finset.card_eq_three] at hX_card
    obtain ⟨a, b, d, hab, had, hbd, hX_eq⟩ := hX_card
    have hc_in : c ∈ ({a, b, d} : Finset V) := hX_eq ▸ hc
    have hu_in : u ∈ ({a, b, d} : Finset V) := hX_eq ▸ hu_X
    have hw_in : w ∈ ({a, b, d} : Finset V) := hX_eq ▸ hw_X
    have hcu : c ≠ u := hu_ne_c.symm
    have hcw : c ≠ w := hw_ne_c.symm
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hc_in; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw_in; tauto
    · intro hx
      rw [← hX_eq]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> [exact hc; exact hu_X; exact hw_X]
  have hv_uw : v = u ∨ v = w := by
    rw [hX_form] at hv_X
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_X
    rcases hv_X with rfl | rfl | rfl
    · exact absurd rfl hv_ne_c
    · left; rfl
    · right; rfl
  have hcv_edge : Sym2.mk (c, v) ∈ T.sym2 := by
    simp only [Finset.mem_sym2_iff]
    constructor
    · exact hc_in_T
    · exact hv_T
  cases hv_uw with
  | inl hvu => left; rw [he₁_eq, ← hvu]; exact hcv_edge
  | inr hvw => right; rw [he₂_eq, ← hvw]; exact hcv_edge

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
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
- Category 2: Each X-external is covered by e₁_X or e₂_X (proven in slot306)
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
  /-
  PROOF SKETCH:
  1. For each X ∈ M, apply two_edges_cover_all_externals to get 2 edges
  2. Union of these edges has ≤ 8 elements
  3. Every triangle is covered:
     - M-elements covered by their own edges
     - Externals covered by two_edges_cover_all_externals
     - Bridge triangles covered because they pass through shared vertices,
       and shared vertices are covered by adjacent elements' edges
  -/
  sorry

end
