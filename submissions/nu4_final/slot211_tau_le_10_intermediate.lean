/-
Tuza ν=4: τ ≤ 10 Intermediate Bound (Slot 211)

GOAL: Prove an intermediate bound τ ≤ 10 that's easier than τ ≤ 8.

MOTIVATION:
  - τ ≤ 8 requires the full fan apex machinery (slots 201-203)
  - τ ≤ 12 is trivially proven (use all M-edges)
  - τ ≤ 10 is a meaningful intermediate result

STRATEGY:
  At each shared vertex v, instead of 2 spokes (optimal), use 3 spokes.
  - 4 shared vertices × 2 spokes = 8 edges (optimal but hard to prove)
  - 4 shared vertices × 2.5 spokes ≈ 10 edges (intermediate)

  Actually, we can be more precise:
  - Each M-element has 3 edges
  - 4 M-elements share some edges at shared vertices
  - In cycle_4: 4 shared vertices, each shared by 2 M-elements
  - Each M-element has 2 shared edges and 1 private edge

  Cover construction:
  - Include all 4 private edges (1 per M-element)
  - At each shared vertex, include 2 spokes (diagonal strategy)
  - But diagonal strategy fails! (see ROUND7_SUBMISSION_PLAN.md)

  ALTERNATIVE: Include 3 edges per M-element, but share cleverly
  - Each M-element contributes 3 edges
  - But edges at shared vertices are shared between 2 M-elements
  - 4 × 3 = 12 edges, minus 4 shared vertices × 1 shared edge = 8 edges?
  - Wait, this doesn't work because edges might not align.

  SIMPLER APPROACH:
  - Use 2 edges for each of A, B (pair 1)
  - Use 3 edges for each of C, D (pair 2, conservative)
  - Total: 2 + 2 + 3 + 3 = 10 edges

  This requires: A-B pair uses 2 edges each via fan apex, C-D uses 3 edges each (all M-edges).
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
-- CYCLE_4 CONFIGURATION
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

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: 2 edges cover A+externals (from slot203)
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
-- CONSERVATIVE BOUND: 3 edges cover any M-element + externals
-- ══════════════════════════════════════════════════════════════════════════════

/-- All 3 edges of M-element A cover A and its externals (trivially) -/
lemma three_edges_cover_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∃ C : Finset (Sym2 V), C ⊆ G.edgeFinset ∧ C.card ≤ 3 ∧
      (∀ t ∈ G.cliqueFinset 3, sharesEdgeWith t A → ∃ e ∈ C, e ∈ t.sym2) := by
  -- C = A.sym2 (all 3 edges of A)
  use A.sym2
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1.1 hA
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).2
  refine ⟨?_, ?_, ?_⟩
  · -- A.sym2 ⊆ G.edgeFinset
    intro e he
    rw [Finset.mem_sym2_iff] at he
    obtain ⟨ha, hb, hab⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    have hA_is_clique := (SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).1
    exact hA_is_clique.2 ha hb hab
  · -- |A.sym2| ≤ 3
    rw [Finset.card_sym2, hA_card]
    native_decide
  · -- Coverage
    intro t ht h_share
    obtain ⟨u, v, huv, hu_t, hv_t, hu_A, hv_A⟩ := h_share
    use s(u, v)
    constructor
    · rw [Finset.mem_sym2_iff]; exact ⟨hu_A, hv_A, huv⟩
    · rw [Finset.mem_sym2_iff]; exact ⟨hu_t, hv_t, huv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 10
-- ══════════════════════════════════════════════════════════════════════════════

/-- Intermediate bound: τ ≤ 10 for cycle_4 -/
theorem tau_le_10_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 10 := by
  have hM_card : M.card = 4 := by
    rw [cfg.hM_eq]
    sorry  -- Aristotle: show {A,B,C,D} has card 4

  -- Use 2 edges for A and B, 3 edges for C and D
  obtain ⟨C_A, hC_A_sub, hC_A_card, hC_A_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.A cfg.hA
  obtain ⟨C_B, hC_B_sub, hC_B_card, hC_B_cover⟩ := two_edges_cover_A G M hM hM_card hν cfg.B cfg.hB
  obtain ⟨C_C, hC_C_sub, hC_C_card, hC_C_cover⟩ := three_edges_cover_A G M hM cfg.C cfg.hC
  obtain ⟨C_D, hC_D_sub, hC_D_card, hC_D_cover⟩ := three_edges_cover_A G M hM cfg.D cfg.hD

  let C := C_A ∪ C_B ∪ C_C ∪ C_D

  have hC_card : C.card ≤ 10 := by
    calc C.card ≤ C_A.card + C_B.card + C_C.card + C_D.card := by
      have h1 := Finset.card_union_le C_A C_B
      have h2 := Finset.card_union_le (C_A ∪ C_B) C_C
      have h3 := Finset.card_union_le (C_A ∪ C_B ∪ C_C) C_D
      omega
    _ ≤ 2 + 2 + 3 + 3 := by omega
    _ = 10 := by norm_num

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
    have h_shares : sharesEdgeWith t X := by
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hX_share
      exact ⟨u, v, huv,
             (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
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
    _ ≤ 10 := hC_card

end
