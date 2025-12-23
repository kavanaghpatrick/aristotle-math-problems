/-
Tuza ν=4: tau_pair_le_4 via V-decomposition
Slot 18 - Scaffolded with tau_union_le_sum (proven in slot16)

Strategy:
- V-decomposition: τ(T_e ∪ T_f) ≤ τ(containing v) + τ(avoiding v)
- τ(containing v) ≤ 2 (triangles share vertex v)
- τ(avoiding v) ≤ 2 (triangles live on ≤4 vertices)
- Therefore τ(T_e ∪ T_f) ≤ 4
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

/-- Key lemma: τ(A ∪ B) ≤ τ(A) + τ(B). PROVEN in slot16 (uuid: b4f73fa3-9cbc-4877-9819-f5e077da1c54) -/
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

/-- Partition lemma: triangles = (containing v) ∪ (avoiding v). PROVEN. -/
lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

/-- V-decomposition: τ(T) ≤ τ(containing v) + τ(avoiding v). Follows from tau_union_le_sum. -/
theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  rw [v_decomposition_union triangles v]
  exact tau_union_le_sum G _ _

/-- Triangles all containing vertex v can be covered by 2 edges incident to v -/
lemma tau_containing_vertex_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V)
    (htri : triangles ⊆ G.cliqueFinset 3)
    (hv : ∀ t ∈ triangles, v ∈ t) :
    triangleCoveringNumberOn G triangles ≤ 2 := by
  sorry

/-- Triangles on ≤4 vertices can be covered by 2 edges -/
lemma tau_on_four_vertices_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (W : Finset V) (hW : W.card ≤ 4)
    (htri_sub : ∀ t ∈ triangles, t ⊆ W) :
    triangleCoveringNumberOn G triangles ≤ 2 := by
  sorry

/-- The pairwise bound: τ(T_e ∪ T_f) ≤ 4 when e,f share exactly vertex v -/
theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

end
