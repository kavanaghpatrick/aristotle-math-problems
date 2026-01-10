/-
Tuza ν=4: τ ≤ 8 Without Bridges (Slot 206)

GOAL: Prove τ ≤ 8 for configurations with no bridges (scattered, path_4 endpoints).

STRATEGY:
  In the "no bridges" case:
  - Each triangle is either in M or external to exactly one M-element
  - 2 edges per M-element cover A and its externals (from slot203)
  - 4 M-elements × 2 edges = 8 edges total

APPLICABILITY:
  - Scattered (ν=4, all disjoint): No shared vertices ⟹ no bridges
  - Star configurations: All share one vertex, but bridges might exist
  - Path_4 endpoints (D-A): No edge between D and A in the intersection graph

NOTE: This is a simpler case than full cycle_4. We separate it to get a partial victory.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

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
-- SCATTERED CONFIGURATION (All disjoint)
-- ══════════════════════════════════════════════════════════════════════════════

structure Scattered (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  h_AB : A ∩ B = ∅
  h_AC : A ∩ C = ∅
  h_AD : A ∩ D = ∅
  h_BC : B ∩ C = ∅
  h_BD : B ∩ D = ∅
  h_CD : C ∩ D = ∅

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA (from slot139)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  sorry  -- PROVEN in slot139

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: 2 edges cover A and externals
-- ══════════════════════════════════════════════════════════════════════════════

axiom two_edges_cover_A_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ C : Finset (Sym2 V), C ⊆ G.edgeFinset ∧ C.card ≤ 2 ∧
      (∀ t ∈ G.cliqueFinset 3, sharesEdgeWith t A → ∃ e ∈ C, e ∈ t.sym2)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCATTERED: Every non-M triangle is external to exactly one M-element
-- ══════════════════════════════════════════════════════════════════════════════

lemma scattered_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Scattered G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_notM : t ∉ M) :
    ∃! X, X ∈ M ∧ sharesEdgeWith t X := by
  -- t shares edge with some X ∈ M (by maximality)
  obtain ⟨X, hX_M, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- Convert card ≥ 2 to sharesEdgeWith
  have h_shares : sharesEdgeWith t X := by
    have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
    have hX_card : X.card = 3 := by
      have : X ∈ G.cliqueFinset 3 := hM.1.1 hX_M
      exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hX_share
    exact ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
           (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩
  -- X is unique: if Y ≠ X also shared edge with t, then t ∩ X and t ∩ Y overlap
  -- But X ∩ Y = ∅ in scattered, so t would need ≥ 4 vertices. Contradiction.
  use X
  refine ⟨⟨hX_M, h_shares⟩, ?_⟩
  intro Y ⟨hY_M, hY_shares⟩
  by_contra hXY
  -- X ≠ Y, both in M, both share edge with t
  -- In scattered: X ∩ Y = ∅
  have h_XY_disj : X ∩ Y = ∅ := by
    rw [cfg.hM_eq] at hX_M hY_M
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX_M hY_M
    rcases hX_M with rfl | rfl | rfl | rfl <;>
    rcases hY_M with rfl | rfl | rfl | rfl <;>
    try exact absurd rfl hXY <;>
    first | exact cfg.h_AB | exact cfg.h_AC | exact cfg.h_AD |
          exact cfg.h_BC | exact cfg.h_BD | exact cfg.h_CD |
          exact Finset.inter_comm _ _ ▸ cfg.h_AB |
          exact Finset.inter_comm _ _ ▸ cfg.h_AC |
          exact Finset.inter_comm _ _ ▸ cfg.h_AD |
          exact Finset.inter_comm _ _ ▸ cfg.h_BC |
          exact Finset.inter_comm _ _ ▸ cfg.h_BD |
          exact Finset.inter_comm _ _ ▸ cfg.h_CD
  -- t shares edge with both X and Y (disjoint), so t needs ≥ 4 vertices
  obtain ⟨u₁, v₁, huv₁, hu₁_t, hv₁_t, hu₁_X, hv₁_X⟩ := h_shares
  obtain ⟨u₂, v₂, huv₂, hu₂_t, hv₂_t, hu₂_Y, hv₂_Y⟩ := hY_shares
  -- {u₁, v₁} ⊆ t ∩ X and {u₂, v₂} ⊆ t ∩ Y
  -- (t ∩ X) ∩ (t ∩ Y) ⊆ t ∩ (X ∩ Y) = t ∩ ∅ = ∅
  have h_tXY_disj : Disjoint (t ∩ X) (t ∩ Y) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    calc (t ∩ X) ∩ (t ∩ Y) = t ∩ X ∩ Y := by ext x; simp [Finset.mem_inter]; tauto
       _ = t ∩ (X ∩ Y) := by ext x; simp [Finset.mem_inter]; tauto
       _ = t ∩ ∅ := by rw [h_XY_disj]
       _ = ∅ := Finset.inter_empty t
  -- |t| ≥ |{u₁,v₁}| + |{u₂,v₂}| = 2 + 2 = 4, but |t| = 3
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
  have h_card_ge_4 : t.card ≥ 4 := by
    have h1 : ({u₁, v₁} : Finset V) ⊆ t ∩ X := by
      intro x hx; simp at hx; rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hu₁_t, hu₁_X⟩
      · exact Finset.mem_inter.mpr ⟨hv₁_t, hv₁_X⟩
    have h2 : ({u₂, v₂} : Finset V) ⊆ t ∩ Y := by
      intro x hx; simp at hx; rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hu₂_t, hu₂_Y⟩
      · exact Finset.mem_inter.mpr ⟨hv₂_t, hv₂_Y⟩
    calc t.card ≥ ((t ∩ X) ∪ (t ∩ Y)).card := Finset.card_le_card (by
           intro x hx; simp at hx; rcases hx with ⟨hxT, _⟩ | ⟨hxT, _⟩ <;> exact hxT)
       _ = (t ∩ X).card + (t ∩ Y).card := Finset.card_union_of_disjoint h_tXY_disj
       _ ≥ ({u₁, v₁} : Finset V).card + ({u₂, v₂} : Finset V).card := by
           have := Finset.card_le_card h1
           have := Finset.card_le_card h2
           omega
       _ = 2 + 2 := by simp [huv₁, huv₂]
       _ = 4 := by norm_num
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for Scattered
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_scattered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (cfg : Scattered G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Get covers for each M-element
  have hM_card : M.card = 4 := by
    rw [cfg.hM_eq]
    sorry  -- Aristotle: show {A,B,C,D} has card 4 using distinctness
  obtain ⟨C_A, hC_A_sub, hC_A_card, hC_A_cover⟩ :=
    two_edges_cover_A_and_externals G M hM hM_card hν cfg.A cfg.hA
  obtain ⟨C_B, hC_B_sub, hC_B_card, hC_B_cover⟩ :=
    two_edges_cover_A_and_externals G M hM hM_card hν cfg.B cfg.hB
  obtain ⟨C_C, hC_C_sub, hC_C_card, hC_C_cover⟩ :=
    two_edges_cover_A_and_externals G M hM hM_card hν cfg.C cfg.hC
  obtain ⟨C_D, hC_D_sub, hC_D_card, hC_D_cover⟩ :=
    two_edges_cover_A_and_externals G M hM hM_card hν cfg.D cfg.hD

  let C := C_A ∪ C_B ∪ C_C ∪ C_D
  have hC_card : C.card ≤ 8 := by
    calc C.card ≤ C_A.card + C_B.card + C_C.card + C_D.card := by
      have h1 := Finset.card_union_le C_A C_B
      have h2 := Finset.card_union_le (C_A ∪ C_B) C_C
      have h3 := Finset.card_union_le (C_A ∪ C_B ∪ C_C) C_D
      omega
    _ ≤ 2 + 2 + 2 + 2 := by omega
    _ = 8 := by norm_num

  have hC_sub : C ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_union] at he
    rcases he with he | he | he | he
    · exact hC_A_sub he
    · exact hC_B_sub he
    · exact hC_C_sub he
    · exact hC_D_sub he

  -- Every triangle shares edge with exactly one M-element (in scattered)
  -- and is covered by that element's cover
  have hC_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ C, e ∈ t.sym2 := by
    intro t ht
    obtain ⟨X, hX_M, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
    -- Convert to sharesEdgeWith
    have h_shares : sharesEdgeWith t X := by
      have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hX_share
      exact ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
             (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩
    rw [cfg.hM_eq] at hX_M
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX_M
    rcases hX_M with rfl | rfl | rfl | rfl
    · obtain ⟨e, he_C, he_t⟩ := hC_A_cover t ht h_shares
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ he_C)), he_t⟩
    · obtain ⟨e, he_C, he_t⟩ := hC_B_cover t ht h_shares
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ he_C)), he_t⟩
    · obtain ⟨e, he_C, he_t⟩ := hC_C_cover t ht h_shares
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he_C), he_t⟩
    · obtain ⟨e, he_C, he_t⟩ := hC_D_cover t ht h_shares
      exact ⟨e, Finset.mem_union_right _ he_C, he_t⟩

  have hC_valid : isTriangleCover G C := ⟨hC_sub, hC_covers⟩
  have hC_in : C ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hC_sub, hC_valid⟩

  unfold triangleCoveringNumber
  have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨C, hC_in⟩
  have h_in_image : C.card ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card :=
    Finset.mem_image_of_mem _ hC_in
  have h_min_le := Finset.min'_le _ C.card h_in_image
  calc (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0
    ≤ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min' (Finset.Nonempty.image h_nonempty _) := by
      simp only [Finset.min_eq_min']; rfl
    _ ≤ C.card := h_min_le
    _ ≤ 8 := hC_card

end
