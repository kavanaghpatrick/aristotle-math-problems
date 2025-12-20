/-
Tuza ν=2: Following Parker's Actual Proof (arXiv:2406.06501)

Parker's approach for ν=2:
1. Either {e,f} are vertex-disjoint ("disconnected")
2. Or |e ∩ f| = 1 (share exactly one vertex)

Case 1 (disconnected): τ(T_e) ≤ 2 and τ(T_f) ≤ 2 directly, since T_e = S_e
Case 2 (connected): Structural analysis shows τ ≤ 4
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E => ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

-- Two triangles are disconnected (vertex-disjoint)
def disconnected (e f : Finset V) : Prop := Disjoint e f

-- Two triangles are connected (share exactly one vertex)
def connected (e f : Finset V) : Prop := (e ∩ f).card = 1

-- Parker Case 1: Disconnected matching
lemma tuza_nu2_disconnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f)
    (hcard : M.card = 2) (h_disj : disconnected e f) :
    triangleCoveringNumber G ≤ 4 := by
  sorry

-- Parker Case 2: Connected matching (share exactly one vertex)
lemma tuza_nu2_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f)
    (hcard : M.card = 2) (h_conn : connected e f) :
    triangleCoveringNumber G ≤ 4 := by
  sorry

-- Main theorem: combine cases
theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

end
