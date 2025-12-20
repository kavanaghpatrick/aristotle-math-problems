/-
Tuza ν=2: Packing choice lemma
For any graph with ν=2, either:
(1) There exists a vertex-disjoint max packing, or
(2) All max packings share vertices, and switching yields disjoint packing
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

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

theorem exists_vertex_disjoint_packing_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : packingNumber G = 2) :
    ∃ M : Finset (Finset V), IsMaxPacking G M ∧
    ∃ e f : Finset V, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ Disjoint e f := by
  sorry

end
