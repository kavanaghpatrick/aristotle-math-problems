/-
Test: Does T_e include e itself?

Test whether e ∈ T_e(e), which should be TRUE since e shares all edges with itself.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

-- Test: For any triangle e in G, is e ∈ T_e(e)?
-- Answer: YES - a triangle shares all its edges with itself
lemma triangle_in_its_T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    e ∈ T_e G e := by
  unfold T_e
  simp only [Finset.mem_filter, he, true_and]
  -- triangleEdges e is nonempty (e has 3 edges)
  have e_card : e.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at he
    exact he.2
  -- So triangleEdges e ∩ triangleEdges e = triangleEdges e ≠ ∅
  rw [Finset.not_disjoint_iff]
  obtain ⟨a, b, c, hab, hbc, hca, rfl⟩ := Finset.card_eq_three.mp e_card
  use s(a, b)
  constructor
  · unfold triangleEdges
    simp only [Finset.mem_image, Finset.mem_offDiag]
    use (a, b)
    simp [hab]
  · unfold triangleEdges
    simp only [Finset.mem_image, Finset.mem_offDiag]
    use (a, b)
    simp [hab]

end
