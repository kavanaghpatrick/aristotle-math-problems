/-
Tuza's Conjecture: τ(T_e) ≤ 2 for PACKING elements

CRITICAL CORRECTION: Previous submission asked about arbitrary triangles.
The flowerGraph counterexample showed τ(T_e) = 3 for the central triangle,
but that triangle is NOT in the maximum packing!

For actual packing elements in flowerGraph:
- M = {{0,1,3}, {1,2,4}, {0,2,5}} with ν = 3
- τ(T_{0,1,3}) = 1 (shares edge {0,1} with {0,1,2})
- τ(T_{1,2,4}) = 1 (shares edge {1,2} with {0,1,2})
- τ(T_{0,2,5}) = 1 (shares edge {0,2} with {0,1,2})

This is what Parker (arXiv:2406.06501) actually proves for ν ≤ 3.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Edge set of a triangle
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun p => Sym2.mk p)

-- Two triangles share an edge
def sharesEdge (t1 t2 : Finset V) : Prop :=
  ¬Disjoint (triangleEdges t1) (triangleEdges t2)

-- Edge-disjoint family
def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

-- Triangle packing number
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

-- Maximum packing predicate
def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M ∧ M.card = trianglePackingNumber G

-- T_e: triangles sharing an edge with e
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => sharesEdge t e)

-- S_e: triangles sharing edge ONLY with e (not other packing elements)
def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → ¬sharesEdge t f)

-- Triangle covering predicate
def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset (Sym2 V)) : Prop :=
  C ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) C

-- Covering number for a subset of triangles
noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : ℕ :=
  (G.edgeFinset.powerset.filter (fun C =>
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) C)).image Finset.card |>.min |>.getD 0

-- Global covering number
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  coveringNumberOn G (G.cliqueFinset 3)

/-
MAIN LEMMA: For e in a maximum packing M with |M| ≤ 3, τ(T_e) ≤ 2

This is the CORRECTED version that applies to packing elements only.
-/
lemma tau_Te_le_2_for_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

/-
Corollary: Tuza's conjecture for ν ≤ 3
Using induction: τ(G) ≤ τ(T_e) + τ(G \ T_e) ≤ 2 + 2(ν-1) = 2ν
-/
theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end
