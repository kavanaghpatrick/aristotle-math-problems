/-
TUZA'S CONJECTURE (1981)

For any graph G:
  ν(G) = maximum number of edge-disjoint triangles
  τ(G) = minimum number of edges to delete to make G triangle-free

Conjecture: τ(G) ≤ 2ν(G)

This is OPEN. Best known: τ ≤ 1.98ν (Haxell-Rödl).
Tight examples exist where τ = 2ν.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped Classical

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

theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end
