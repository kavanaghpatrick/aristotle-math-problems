/-
Parker's Proof of Tuza for ν ≤ 3 (arXiv:2406.06501)
Minimal formalization following Boris pattern.

KEY INSIGHT: Parker uses induction on matching size.
For each e in maximum matching M:
- T_e = triangles sharing edge with e
- S_e = triangles sharing edge with e but not others in M
- Lemma 2.2: ν(S_e) = 1 (any two in S_e share an edge)
- Lemma 2.3: ν(H \ T_e) = ν - 1

The induction gives: τ ≤ τ(T_e) + 2(ν-1)
For Tuza (τ ≤ 2ν), need τ(T_e) ≤ 2.
Paper proves τ(T_e) ≤ 2 for ν ≤ 3 via case analysis.
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

def sharesEdge (t1 t2 : Finset V) : Prop :=
  ¬ Disjoint (triangleEdges t1) (triangleEdges t2)

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h => sharesEdge h e)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h =>
    sharesEdge h e ∧ ∀ f ∈ M, f ≠ e → ¬ sharesEdge h f)

theorem tuza_case_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) : triangleCoveringNumber G ≤ 6 := by
  sorry

theorem tuza_case_nu_2_parker (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

end
