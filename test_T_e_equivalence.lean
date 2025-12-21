/-
Test: Are the two T_e definitions equivalent?

Definition 1 (edge-based): t ∈ T_e iff ¬Disjoint (triangleEdges t) (triangleEdges e)
Definition 2 (vertex-based): t ∈ T_e iff (t ∩ e).card ≥ 2

Both should mean "t shares an edge with e"
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def T_e_edges (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def T_e_vertices (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

-- Are they equivalent?
lemma T_e_definitions_equivalent (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) :
    T_e_edges G e = T_e_vertices G e := by
  ext t
  simp only [T_e_edges, T_e_vertices, Finset.mem_filter]
  constructor
  · intro ⟨ht, hedge⟩
    constructor
    · exact ht
    · -- If triangles share edge, they share ≥2 vertices
      rw [Finset.not_disjoint_iff] at hedge
      obtain ⟨edge, he_t, he_e⟩ := hedge
      -- edge is a Sym2, extract its vertices
      sorry
  · intro ⟨ht, hvert⟩
    constructor
    · exact ht
    · -- If triangles share ≥2 vertices, they share an edge
      rw [Finset.not_disjoint_iff]
      -- Get the shared vertices
      have : (t ∩ e).card ≥ 2 := hvert
      -- There exists a pair of vertices in t ∩ e
      sorry

end
