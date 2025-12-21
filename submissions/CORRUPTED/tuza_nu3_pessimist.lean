/-
Tuza ν ≤ 3: PESSIMIST - Hunt for counterexamples to τ(T_e) ≤ 2

We claim: For e ∈ M (max packing) with |M| ≤ 3, τ(T_e) ≤ 2.

This file asks Aristotle to DISPROVE this by finding:
- A graph G with ν(G) ≤ 3
- A max packing M with some e ∈ M
- Where τ(T_e) ≥ 3

If Aristotle proves the negation, our proof strategy is INVALID.
If Aristotle fails, it provides evidence the lemma might be true.
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

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

theorem tau_Te_counterexample :
    ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
      (e : Finset V) (he : e ∈ M),
    coveringNumberOn G (T_e G e) ≥ 3 := by
  sorry

end
