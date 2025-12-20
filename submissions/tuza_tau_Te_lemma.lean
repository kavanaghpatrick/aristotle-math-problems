/-
Tuza ν≤3: The Missing Lemma
Target: Prove τ(T_e) ≤ 2 for some e ∈ M when ν ≤ 3

This is the gap between:
- tau_S_le_2: τ(S_e) ≤ 2 (PROVEN)
- inductive_bound: τ(G) ≤ τ(T_e) + τ(rest) (PROVEN)

We need: τ(T_e) ≤ 2 for the induction to work.

Key insight: T_e = triangles sharing edge with e
All such triangles share one of the 3 edges of e.
For ν ≤ 3, the structure is constrained enough that τ(T_e) ≤ 2.
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

def IsTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ IsTriangleCover G E}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

-- THE KEY LEMMA: τ(T_e) ≤ 2 for some e when ν ≤ 3
-- For ν = 1: Only one packing element, T_e covers all triangles, τ(T_e) ≤ 2 by star/K4
-- For ν = 2, 3: Can choose e such that T_e has nice structure

lemma exists_e_tau_Te_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3) (hpos : M.Nonempty) :
    ∃ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Alternative: Direct bound for any e when ν ≤ 3
lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Case ν = 1: T_e is all triangles, they all share edge with e
lemma tau_Te_le_2_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Case ν = 2
lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Case ν = 3
lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Main theorem using the lemma
theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  sorry

end
