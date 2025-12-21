/-
PESSIMIST: Hunt for counterexample to "vertex-disjoint packing always exists for ν=2"

The lemma `exists_good_packing_nu2` from file 2fe95b81 claims:
  For any graph with ν = 2, there exists a max packing where elements are vertex-disjoint.

We believe this is FALSE. This submission asks Aristotle to PROVE the negation:
  There exists a graph with ν = 2 where NO max packing has vertex-disjoint elements.

Expected counterexample: Graph with only triangles {1,2,3} and {1,4,5} sharing vertex 1.
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

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def vertexDisjoint (t1 t2 : Finset V) : Prop := Disjoint t1 t2

-- COUNTEREXAMPLE: Find a graph where no max packing has vertex-disjoint elements
theorem no_vertex_disjoint_packing_counterexample :
    ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    packingNumber G = 2 ∧
    ∀ M : Finset (Finset V), IsMaxPacking G M →
      ¬(∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f) := by
  sorry

end
