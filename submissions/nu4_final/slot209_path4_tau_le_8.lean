/-
Tuza ν=4: τ ≤ 8 for Path_4 (Slot 209)

GOAL: Prove τ ≤ 8 for Path_4 configuration (A-B-C-D, no D-A edge).

STRATEGY:
  Path_4 is SIMPLER than Cycle_4:
  - Only 3 adjacencies (A-B, B-C, C-D) instead of 4
  - D ∩ A = ∅, so no D-A bridges (slot208)
  - A-C and B-D are also disjoint, so no bridges there either

ANALYSIS:
  Triangles partition into:
  1. M-elements: {A, B, C, D} - 4 triangles
  2. Externals of A only (share edge with A, not B, C, D)
  3. Externals of B only
  4. Externals of C only
  5. Externals of D only
  6. Bridges A-B (share edge with both A and B)
  7. Bridges B-C
  8. Bridges C-D
  9. NO bridges A-C, B-D, D-A (disjoint pairs)

  Coverage:
  - 2 edges per M-element cover M-element + its externals (slot203)
  - Bridges between adjacent pairs are covered by M-edges (slot205)
  - Total: 4 × 2 = 8 edges
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = ∅  -- KEY: Path_4 has no D-A edge
  hAC : A ∩ C = ∅
  hBD : B ∩ D = ∅

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOMS FROM PREVIOUS SLOTS
-- ══════════════════════════════════════════════════════════════════════════════

axiom two_edges_cover_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ C : Finset (Sym2 V), C ⊆ G.edgeFinset ∧ C.card ≤ 2 ∧
      (∀ t ∈ G.cliqueFinset 3, sharesEdgeWith t A → ∃ e ∈ C, e ∈ t.sym2)

axiom triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER
-- ══════════════════════════════════════════════════════════════════════════════

lemma card_ge_2_implies_shares (t X : Finset V) (h : (t ∩ X).card ≥ 2) :
    sharesEdgeWith t X := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact ⟨u, v, huv,
         (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
         (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for Path_4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (cfg : Path4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- M has exactly 4 elements
  have hM_card : M.card = 4 := by
    rw [cfg.hM_eq]
    sorry  -- Aristotle: show {A,B,C,D} has card 4

  -- Get 2-edge covers for each M-element
  obtain ⟨C_A, hC_A_sub, hC_A_card, hC_A_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.A cfg.hA
  obtain ⟨C_B, hC_B_sub, hC_B_card, hC_B_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.B cfg.hB
  obtain ⟨C_C, hC_C_sub, hC_C_card, hC_C_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.C cfg.hC
  obtain ⟨C_D, hC_D_sub, hC_D_card, hC_D_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.D cfg.hD

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

  have hC_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ C, e ∈ t.sym2 := by
    intro t ht
    obtain ⟨X, hX_M, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
    have h_shares := card_ge_2_implies_shares t X hX_share
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
