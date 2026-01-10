/-
  slot223a_link_graph_small.lean

  LEMMA: At shared vertex v in cycle_4, M-neighbors has at most 4 vertices.

  FROM 3-ROUND DEBATE (Jan 3, 2026):
  This is a foundational lemma for the Link Graph + König approach to τ ≤ 8.

  PROOF IDEA:
  At each shared vertex v (e.g., v_ab):
  - Exactly 2 M-elements contain v (A and B)
  - A = {v_ab, v_da, a_priv} contributes 2 vertices: v_da, a_priv
  - B = {v_ab, v_bc, b_priv} contributes 2 vertices: v_bc, b_priv
  - Total M-neighbors: {v_da, a_priv, v_bc, b_priv} = 4 vertices

  1 SORRY: The main counting argument
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

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
  hM_card : M.card = 4
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  hAC : A ∩ C = ∅
  hBD : B ∩ D = ∅
  -- Membership witnesses
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A

/-- M-neighbors of v: vertices in M-elements containing v, excluding v itself -/
def M_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  M.biUnion (fun X => if v ∈ X then X.erase v else ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS (PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each M-element has exactly 3 vertices -/
lemma M_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X : Finset V) (hX : X ∈ M) : X.card = 3 := by
  have := hM.1 hX
  exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2

/-- At v_ab, only A and B contain v_ab -/
lemma M_elements_at_vab (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    ∀ X ∈ M, cfg.v_ab ∈ X → X = cfg.A ∨ X = cfg.B := by
  intro X hX hvab_X
  rw [cfg.hM_eq] at hX
  simp only [mem_insert, mem_singleton] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · left; rfl
  · right; rfl
  · -- X = C, but v_ab ∉ C
    exfalso
    have hAC := cfg.hAC
    have hvab_A := cfg.h_vab_A
    have : cfg.v_ab ∈ cfg.A ∩ cfg.C := mem_inter.mpr ⟨hvab_A, hvab_X⟩
    rw [hAC] at this
    exact not_mem_empty _ this
  · -- X = D, but v_ab ∉ D
    exfalso
    have hBD := cfg.hBD
    have hvab_B := cfg.h_vab_B
    -- Need to show v_ab ∉ D
    -- D ∩ A = {v_da}, and v_ab ∈ A
    -- If v_ab ∈ D, then v_ab ∈ D ∩ A = {v_da}, so v_ab = v_da
    -- But A ∩ B = {v_ab} and D ∩ A = {v_da}
    -- If v_ab = v_da, then B ∩ D contains v_ab (since v_ab ∈ B and v_da ∈ D)
    -- But B ∩ D = ∅, contradiction
    have hDA := cfg.hDA
    have h : cfg.v_ab ∈ cfg.D ∩ cfg.A := mem_inter.mpr ⟨hvab_X, cfg.h_vab_A⟩
    rw [hDA] at h
    simp only [mem_singleton] at h
    -- h : v_ab = v_da
    have hvda_D := cfg.h_vda_D
    have hvab_B := cfg.h_vab_B
    have : cfg.v_ab ∈ cfg.B ∩ cfg.D := mem_inter.mpr ⟨hvab_B, h ▸ hvda_D⟩
    rw [hBD] at this
    exact not_mem_empty _ this

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- At shared vertex v in cycle_4, the link graph has at most 4 vertices -/
theorem link_graph_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    (M_neighbors G M v).card ≤ 4 := by
  -- At each shared vertex, exactly 2 M-elements meet
  -- Each contributes 2 other vertices (triangle has 3, minus the shared vertex)
  -- Total: 4 M-neighbors
  -- At each shared vertex, exactly 2 M-elements contain v
  -- Each M-element is a 3-set, contributing 2 other vertices
  -- M_neighbors = union of (X \ {v}) for X containing v
  -- Since only 2 M-elements contain v, and each contributes 2 vertices:
  -- |M_neighbors| ≤ 2 × 2 = 4
  -- (Could be less if the contributed vertices overlap, but they don't in cycle_4)
  sorry

end
