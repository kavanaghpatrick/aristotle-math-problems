/-
Tuza ν=2: Vertex-disjoint packing case
When packing elements share no vertices, T_e = S_e.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ (M : Set (Finset V)).PairwiseDisjoint triangleEdges

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t =>
    ¬Disjoint (triangleEdges t) (triangleEdges e) ∧
    ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f))

theorem Te_eq_Se_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_disj : ∀ f ∈ M, f ≠ e → Disjoint e f) :
    T_e G e = S_e G e M := by
  sorry

end
