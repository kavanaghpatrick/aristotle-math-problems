/-
Tuza ν=4: tau_pair_le_4 via V-decomposition
Boris Minimal with strategic hints

Aristotle: Use V-decomposition on shared vertex v.
- Triangles containing v: cover with 2 edges incident to v
- Triangles avoiding v: live on ≤4 vertices → cover with 2 edges
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

end
