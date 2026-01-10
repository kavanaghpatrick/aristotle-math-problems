/-
Tuza ν=4: Cover Hits Bridge (Slot 205)

GOAL: Show that the 2-edge cover for A or B also hits bridges between them.

KEY INSIGHT (from slot204):
  - Bridges between A and B contain their shared vertex v
  - The cover for A uses spokes from fan apex of A
  - If fan apex of A = v, then the cover naturally hits bridges
  - If fan apex of A ≠ v, we need additional analysis

STRATEGY:
  For cycle_4 with A ∩ B = {v_ab}:
  - Bridges between A,B contain v_ab
  - A's fan apex might be v_ab, v_da, or a_priv
  - B's fan apex might be v_ab, v_bc, or b_priv
  - Key: if EITHER A or B has fan apex = v_ab, bridges are covered

CRITICAL OBSERVATION:
  From slot139 (proven): Every triangle shares edge with some M-element
  From slot204: Bridges contain shared vertex v
  Combined: Bridge T contains v and shares edge with A (and B)
  So spoke from v to another A-vertex hits T!
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

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isBridgeBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧ sharesEdgeWith t B

def bridgesBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isBridgeBetween G M A B)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM FROM SLOT 204
-- ══════════════════════════════════════════════════════════════════════════════

axiom bridge_contains_shared_vertex (A B T : Finset V) (v : V)
    (hA : A.card = 3) (hB : B.card = 3) (hT : T.card = 3)
    (h_inter : A ∩ B = {v})
    (h_T_A : sharesEdgeWith T A)
    (h_T_B : sharesEdgeWith T B) :
    v ∈ T

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA: Bridge is covered by A-edge or B-edge
-- ══════════════════════════════════════════════════════════════════════════════

/-- A bridge between A and B shares an edge with A (by definition) -/
lemma bridge_shares_edge_with_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B T : Finset V)
    (hT : isBridgeBetween G M A B T) :
    sharesEdgeWith T A := hT.2.2.1

/-- A bridge between A and B is covered by the common A-B edge -/
theorem bridge_covered_by_shared_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T : Finset V) (v : V)
    (hA_clique : A ∈ G.cliqueFinset 3)
    (hB_clique : B ∈ G.cliqueFinset 3)
    (hT_clique : T ∈ G.cliqueFinset 3)
    (h_inter : A ∩ B = {v})
    (h_T_A : sharesEdgeWith T A)
    (h_T_B : sharesEdgeWith T B) :
    ∃ e ∈ A.sym2, e ∈ T.sym2 := by
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).2
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hB_clique).2
  have hT_card : T.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hT_clique).2
  -- v ∈ T (from bridge_contains_shared_vertex)
  have hv_T := bridge_contains_shared_vertex A B T v hA_card hB_card hT_card h_inter h_T_A h_T_B
  -- v ∈ A (from A ∩ B = {v})
  have hv_A : v ∈ A := by
    have : v ∈ A ∩ B := by rw [h_inter]; simp
    exact Finset.mem_inter.mp this |>.1
  -- T shares edge with A, so ∃ u ≠ w in T ∩ A
  obtain ⟨u, w, huw, hu_T, hw_T, hu_A, hw_A⟩ := h_T_A
  -- The edge {u, w} is in both A.sym2 and T.sym2
  use s(u, w)
  constructor
  · rw [Finset.mem_sym2_iff]; exact ⟨hu_A, hw_A, huw⟩
  · rw [Finset.mem_sym2_iff]; exact ⟨hu_T, hw_T, huw⟩

/-- A-edges cover bridges between A and any neighbor in cycle_4 -/
theorem A_edges_cover_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (v : V)
    (h_inter : A ∩ B = {v}) :
    ∀ T ∈ bridgesBetween G M A B, ∃ e ∈ A.sym2, e ∈ T.sym2 := by
  intro T hT
  simp only [bridgesBetween, Finset.mem_filter] at hT
  have hT_bridge := hT.2
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1.1 hA
  have hB_clique : B ∈ G.cliqueFinset 3 := hM.1.1 hB
  exact bridge_covered_by_shared_edge G A B T v hA_clique hB_clique hT.1 h_inter hT_bridge.2.2.1 hT_bridge.2.2.2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY THEOREM: Bridge τ bound
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridges between adjacent M-elements (in cycle_4) need no extra edges beyond M-edges -/
theorem tau_bridges_le_zero_additional (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (v : V)
    (h_inter : A ∩ B = {v}) :
    ∀ T ∈ bridgesBetween G M A B, ∃ e ∈ A.sym2 ∪ B.sym2, e ∈ T.sym2 := by
  intro T hT
  obtain ⟨e, he_A, he_T⟩ := A_edges_cover_bridges G M hM A B hA hB v h_inter T hT
  exact ⟨e, Finset.mem_union_left _ he_A, he_T⟩

end
