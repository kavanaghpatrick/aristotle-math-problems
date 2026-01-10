/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8d682a7a-526f-460b-b6d0-f7ec169553b7
-/

/-
  slot223e_cover_to_edges_v2.lean

  LEMMA: A vertex cover of L_v gives an edge cover for triangles through v
         where both other vertices are in M_neighbors(v).

  PREVIOUS VERSION WAS FALSE!
  The old version claimed to cover ALL triangles through v, but only had
  hypotheses about triangles with both other vertices in M_neighbors(v).
  Aristotle found counterexample: triangle {0,1,2} through v=0 where
  1,2 are NOT M_neighbors of 0.

  CORRECTED VERSION:
  We explicitly restrict to triangles T = {v, u, w} where u, w ∈ M_neighbors(v).
  This is the correct domain for the Link Graph approach.

  In cycle_4, this restriction is NOT limiting because:
  - Every triangle shares an edge with some M-element (maximality)
  - At shared vertex v, triangles through v that share edge with M-element
    containing v have both other vertices related to M_neighbors(v)

  1 SORRY: The restricted edge cover construction
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- M-neighbors of v: vertices in M-elements containing v, excluding v itself -/
def M_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  M.biUnion (fun X => if v ∈ X then X.erase v else ∅)

/-- Triangles through v with both other vertices in a given set S -/
def trianglesThroughVinS (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : Finset (Finset V) :=
  G.cliqueFinset 3 |>.filter (fun T => v ∈ T ∧ ∀ x ∈ T, x = v ∨ x ∈ S)

/-- Edges from v to vertices in C -/
def spokesFromV (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : Finset V) : Finset (Sym2 V) :=
  C.biUnion (fun c => if G.Adj v c then {s(v, c)} else ∅)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

No goals to be solved
No goals to be solved-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA (CORRECTED)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A vertex cover of the link graph L_v gives edge cover for triangles
    through v where both other vertices are in M_neighbors(v).

    Let S = M_neighbors(v).
    Let C ⊆ S be a vertex cover of L_v (the link graph at v).

    Then the edges {v, c} for c ∈ C cover all triangles T = {v, u, w}
    where u, w ∈ S.

    PROOF:
    Let T = {v, u, w} with u, w ∈ S.
    Since T is a triangle, {u, w} is an edge in L_v.
    Since C is a vertex cover of L_v, u ∈ C or w ∈ C.
    WLOG u ∈ C. Then edge {v, u} covers T. ∎ -/
theorem vertex_cover_to_edge_cover_restricted (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (C : Finset V)
    (hC_subset : C ⊆ S)
    -- C is a vertex cover of the link graph (edges within S that form triangles with v)
    (hC_cover : ∀ u w, u ∈ S → w ∈ S → u ≠ w → G.Adj u w → G.Adj v u → G.Adj v w →
                       u ∈ C ∨ w ∈ C) :
    ∀ T ∈ trianglesThroughVinS G v S, ∃ e ∈ spokesFromV G v C, e ∈ T.sym2 := by
  intro T hT
  simp only [trianglesThroughVinS, mem_filter] at hT
  obtain ⟨hT_tri, hv_in, hT_in_S⟩ := hT
  -- T is a triangle containing v with all other vertices in S
  -- Extract u, w ∈ S \ {v} such that T = {v, u, w}
  have hT_card : T.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hT_tri).2
  -- T = {v, u, w} for some u ≠ v, w ≠ v, u ≠ w
  -- Since T has 3 elements and v ∈ T, there exist exactly 2 other elements
  have h_exists : ∃ u w, u ∈ T ∧ w ∈ T ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w ∧
                         T = {v, u, w} := by
    sorry  -- Combinatorial extraction
  obtain ⟨u, w, hu_in, hw_in, huv, hwv, huw, hT_eq⟩ := h_exists
  -- u, w ∈ S (by hT_in_S)
  have hu_S : u ∈ S := by
    have := hT_in_S u hu_in
    rcases this with rfl | h; exact absurd rfl huv; exact h
  have hw_S : w ∈ S := by
    have := hT_in_S w hw_in
    rcases this with rfl | h; exact absurd rfl hwv; exact h
  -- {u, w} is an edge in the link graph (they're adjacent and both adj to v)
  have h_adj_uw : G.Adj u w := by
    have hT_clique := (SimpleGraph.mem_cliqueFinset_iff.mp hT_tri).1
    exact hT_clique (by rw [hT_eq]; simp) (by rw [hT_eq]; simp) huw
  have h_adj_vu : G.Adj v u := by
    have hT_clique := (SimpleGraph.mem_cliqueFinset_iff.mp hT_tri).1
    exact hT_clique (by rw [hT_eq]; simp) (by rw [hT_eq]; simp) huv.symm
  have h_adj_vw : G.Adj v w := by
    have hT_clique := (SimpleGraph.mem_cliqueFinset_iff.mp hT_tri).1
    exact hT_clique (by rw [hT_eq]; simp) (by rw [hT_eq]; simp) hwv.symm
  -- By vertex cover, u ∈ C or w ∈ C
  have h_cover := hC_cover u w hu_S hw_S huw h_adj_uw h_adj_vu h_adj_vw
  rcases h_cover with hu_C | hw_C
  · -- u ∈ C, use edge {v, u}
    use s(v, u)
    constructor
    · simp only [spokesFromV, mem_biUnion]
      use u, hu_C
      simp [h_adj_vu]
    · rw [hT_eq]
      simp [Finset.sym2_insert]
      left; left; rfl
  · -- w ∈ C, use edge {v, w}
    use s(v, w)
    constructor
    · simp only [spokesFromV, mem_biUnion]
      use w, hw_C
      simp [h_adj_vw]
    · rw [hT_eq]
      simp [Finset.sym2_insert]
      left; right; left; rfl

/-- The number of covering edges is at most |C| -/
lemma spokes_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (C : Finset V) :
    (spokesFromV G v C).card ≤ C.card := by
  unfold spokesFromV
  apply card_biUnion_le

end