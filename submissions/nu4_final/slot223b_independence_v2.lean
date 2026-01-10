/-
  slot223b_independence_v2.lean

  LEMMA: The link graph at shared vertex v has independence number ≥ 2.

  PROOF STRATEGY (5-packing contradiction via slot182):

  At v_ab, suppose α(L_v) = 1 (L_v is complete on 4 vertices).
  Then all C(4,2) = 6 pairs of M-neighbors form triangles with v_ab.

  At most 2 of these are M-elements (A and B).
  The other 4 are externals.

  Consider externals of A = {v_ab, v_da, a_priv}:
  - T1 = {v_ab, v_da, v_bc}:   T1 ∩ A = {v_ab, v_da} (edge-sharing with A)
  - T3 = {v_ab, a_priv, v_bc}: T3 ∩ A = {v_ab, a_priv} (edge-sharing with A)

  T1 ∩ T3 = {v_ab} - only 1 vertex!
  But slot182 says externals of A must share an edge.
  Contradiction!

  Therefore α(L_v) ≥ 2.

  1 SORRY for Aristotle.
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

/-- M-neighbors of v: vertices in M-elements containing v, excluding v itself -/
def M_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  M.biUnion (fun X => if v ∈ X then X.erase v else ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- SLOT182 AXIOM (PROVEN SEPARATELY)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two externals of the same M-element share an edge -/
axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V)
    (hT₁ : T₁ ∈ G.cliqueFinset 3 ∧ T₁ ∉ M ∧ (T₁ ∩ X).card ≥ 2)
    (hT₂ : T₂ ∈ G.cliqueFinset 3 ∧ T₂ ∉ M ∧ (T₂ ∩ X).card ≥ 2)
    (h_ne : T₁ ≠ T₂) :
    (T₁ ∩ T₂).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA: Independence ≥ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- At a shared vertex v in cycle_4, there exist two non-adjacent M-neighbors.

    In other words, there exist u, w ∈ M_neighbors such that
    {v, u, w} is NOT a triangle in G.

    This means the link graph L_v is not complete, hence α(L_v) ≥ 2.

    PROOF BY CONTRADICTION:
    Suppose L_v is complete. At v_ab with M_neighbors = {v_da, a', v_bc, b'},
    all 6 triangles through v_ab exist. This creates 4 externals of A.
    By slot182, any 2 externals of A share an edge.
    But T1 = {v_ab, v_da, v_bc} and T3 = {v_ab, a', v_bc} only share {v_ab}.
    Contradiction. -/
theorem link_graph_independence_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (v : V) (S : Finset V) (hS : S = M_neighbors G M v) (hS_card : S.card = 4) :
    ∃ u w, u ∈ S ∧ w ∈ S ∧ u ≠ w ∧ ¬({v, u, w} ∈ G.cliqueFinset 3) := by
  -- Proof by contradiction
  by_contra h_all_triangles
  push_neg at h_all_triangles
  -- h_all_triangles : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → {v, u, w} ∈ G.cliqueFinset 3
  -- This means all C(4,2) = 6 pairs of S-elements form triangles with v.
  --
  -- We need to find two externals of some M-element X such that they
  -- only intersect at v (not at an edge), contradicting slot182.
  --
  -- At v, there are exactly 2 M-elements containing v.
  -- The other 4 triangles through v are externals of those M-elements.
  -- Use slot182 to derive contradiction.
  sorry

end
