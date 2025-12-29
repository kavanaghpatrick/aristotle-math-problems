/-
`slot83` isolates the supporting-edge lemma used whenever a triangle shares an edge with
one of the packing triangles.  This ensures the local covers extracted per shared vertex
actually touch the triangles that need covering.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Auxiliary triangle families: triangles sharing an edge with `t`. -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun x => (x ∩ t).card ≥ 2

/-- Local edge multiset for a vertex: all packing edges that touch `v`. -/
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- Target lemma: triangles that share an edge with a packing triangle `A` and contain a
    vertex `v ∈ A` necessarily contain one of the `M_edges_at` edges through `v`.  This is
    the support condition plugged into `local_cover_le_2` during the final tau bound. -/
lemma cycle4_triangle_at_vertex_supported (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (hA : A ∈ M)
    (v : V) (hv : v ∈ A)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G A) (hvt : v ∈ t) :
    ∃ e ∈ M_edges_at G M v, e ∈ t.sym2 := by
  -- Aristotle ports the supporting-edge argument from slot73 here.
  sorry
