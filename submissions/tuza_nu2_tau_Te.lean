/-
Tuza ν=2: τ(T_e) ≤ 2 via packing choice
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E => ∀ t ∈ triangles, ∃ e ∈ E, e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

theorem tau_Te_le_2_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 2) :
    ∃ M : Finset (Finset V), isMaxPacking G M ∧
    ∃ e ∈ M, triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry

end
