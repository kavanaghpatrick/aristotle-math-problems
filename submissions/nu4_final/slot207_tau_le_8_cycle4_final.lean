/-
Tuza ν=4: τ ≤ 8 for Cycle_4 (FINAL ASSEMBLY) (Slot 207)

GOAL: Complete the τ ≤ 8 proof for cycle_4 configuration.

STRATEGY (Combining all previous slots):
  1. Each M-element A needs 2 edges to cover A + externals (slot201-203)
  2. Bridges between adjacent pairs (A-B, B-C, C-D, D-A) are handled by M-edges (slot204-205)
  3. No bridges between non-adjacent pairs in cycle_4 (A-C, B-D share no vertex)
  4. Total: 4 × 2 = 8 edges

CRITICAL CHECK:
  The 4+4 approach is INVALID (see FALSE_LEMMAS.md Pattern 6).
  But 2 edges per M-element IS valid because:
  - Externals of A share common A-vertex (slot201)
  - 2 edges from A.sym2 cover A and externals
  - Bridges are covered by same A.sym2 edges (slot205)

KEY INSIGHT:
  We DON'T need extra edges for bridges because bridges share edge with M-elements!
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
-- CYCLE_4 CONFIGURATION (from slot139 PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
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
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  -- Non-adjacency in cycle (A-C and B-D don't share vertex)
  hAC : A ∩ C = ∅
  hBD : B ∩ D = ∅
  -- Distinctness of shared vertices
  h_distinct_ab_bc : v_ab ≠ v_bc
  h_distinct_bc_cd : v_bc ≠ v_cd
  h_distinct_cd_da : v_cd ≠ v_da
  h_distinct_da_ab : v_da ≠ v_ab

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOMS FROM PREVIOUS SLOTS
-- ══════════════════════════════════════════════════════════════════════════════

/-- AXIOM (slot203): 2 edges cover A and triangles sharing edge with A -/
axiom two_edges_cover_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ C : Finset (Sym2 V), C ⊆ G.edgeFinset ∧ C.card ≤ 2 ∧
      (∀ t ∈ G.cliqueFinset 3, sharesEdgeWith t A → ∃ e ∈ C, e ∈ t.sym2)

/-- AXIOM (slot139): Every triangle shares edge with some M-element -/
axiom triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Card ≥ 2 intersection implies sharesEdgeWith
-- ══════════════════════════════════════════════════════════════════════════════

lemma card_ge_2_implies_shares (t X : Finset V) (h : (t ∩ X).card ≥ 2) :
    sharesEdgeWith t X := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact ⟨u, v, huv,
         (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
         (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for Cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- M has exactly 4 elements
  have hM_card : M.card = 4 := by
    rw [cfg.hM_eq]
    have hAB : cfg.A ≠ cfg.B := by
      intro h
      have := cfg.hAB
      rw [h, Finset.inter_self] at this
      have hB_card : cfg.B.card = 3 := by
        have : cfg.B ∈ G.cliqueFinset 3 := hM.1.1 cfg.hB
        exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
      simp only [Finset.card_singleton] at this ⊢
      sorry  -- Aristotle: card contradiction
    have hAC : cfg.A ≠ cfg.C := by
      intro h; rw [h] at cfg.hAC; simp at cfg.hAC
      have hC_card : cfg.C.card = 3 := by
        have : cfg.C ∈ G.cliqueFinset 3 := hM.1.1 cfg.hC
        exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
      omega
    have hAD : cfg.A ≠ cfg.D := by
      intro h
      have := cfg.hDA
      rw [h, Finset.inter_self] at this
      have hD_card : cfg.D.card = 3 := by
        have : cfg.D ∈ G.cliqueFinset 3 := hM.1.1 cfg.hD
        exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
      simp at this; omega
    have hBC : cfg.B ≠ cfg.C := by
      intro h
      have := cfg.hBC
      rw [h, Finset.inter_self] at this
      have hC_card : cfg.C.card = 3 := by
        have : cfg.C ∈ G.cliqueFinset 3 := hM.1.1 cfg.hC
        exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
      simp at this; omega
    have hBD : cfg.B ≠ cfg.D := by
      intro h; rw [h] at cfg.hBD; simp at cfg.hBD
      have hD_card : cfg.D.card = 3 := by
        have : cfg.D ∈ G.cliqueFinset 3 := hM.1.1 cfg.hD
        exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
      omega
    have hCD : cfg.C ≠ cfg.D := by
      intro h
      have := cfg.hCD
      rw [h, Finset.inter_self] at this
      have hD_card : cfg.D.card = 3 := by
        have : cfg.D ∈ G.cliqueFinset 3 := hM.1.1 cfg.hD
        exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
      simp at this; omega
    simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    simp [hAB, hAC, hAD, hBC, hBD, hCD]
    sorry  -- Aristotle: finish card computation

  -- Get 2-edge covers for each M-element
  obtain ⟨C_A, hC_A_sub, hC_A_card, hC_A_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.A cfg.hA
  obtain ⟨C_B, hC_B_sub, hC_B_card, hC_B_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.B cfg.hB
  obtain ⟨C_C, hC_C_sub, hC_C_card, hC_C_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.C cfg.hC
  obtain ⟨C_D, hC_D_sub, hC_D_card, hC_D_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.D cfg.hD

  -- Union of covers
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
    -- t shares edge with some X ∈ M
    obtain ⟨X, hX_M, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
    have h_shares := card_ge_2_implies_shares t X hX_share
    -- X ∈ {A, B, C, D}
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

  -- C is a valid cover
  have hC_valid : isTriangleCover G C := ⟨hC_sub, hC_covers⟩
  have hC_in : C ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hC_sub, hC_valid⟩

  -- τ ≤ |C| ≤ 8
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
