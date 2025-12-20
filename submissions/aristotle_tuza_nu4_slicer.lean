/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8026542a-86a0-4ed4-a1f5-8f1e1595504e

The following was proved by Aristotle:

- theorem tuza_K4_free_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK4 : IsK4Free G) (hnu : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8
-/

/-
Tuza ν=4: The Slicer
Prove Tuza for K₄-free graphs (isolate dense obstructions)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

def IsK4Free (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.cliqueFinset 4 = ∅

/- Aristotle failed to find a proof. -/
theorem tuza_K4_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK4 : IsK4Free G) : triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

theorem tuza_K4_free_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK4 : IsK4Free G) (hnu : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8 := by
  -- Apply the theorem tuza_K4_free with the given hypotheses.
  have := tuza_K4_free G hK4;
  aesop

end