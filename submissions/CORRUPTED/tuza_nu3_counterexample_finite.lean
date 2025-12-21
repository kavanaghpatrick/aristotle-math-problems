/-
Tuza ν ≤ 3: Finite counterexample search

Search for counterexamples on small vertex sets (≤ 9 vertices).
If τ(T_e) ≤ 2 fails for ANY e ∈ M with |M| ≤ 3, this will find it.
-/

import Mathlib

set_option maxHeartbeats 800000

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

theorem no_counterexample_6_vertices :
    ∀ (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 6))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

theorem no_counterexample_7_vertices :
    ∀ (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 7))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

theorem no_counterexample_8_vertices :
    ∀ (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 8))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

theorem no_counterexample_9_vertices :
    ∀ (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 9))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

end
