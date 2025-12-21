/-
Test: Does coveringNumberOn allow non-graph edges?

We construct an example where Definition A (unrestricted) gives a different
answer than Definition B (restricted to G.edgeFinset).
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

-- Simple 3-vertex example
inductive ThreeVertex | A | B | C
deriving Fintype, DecidableEq

open ThreeVertex

-- Graph with only edge {A,B}, missing {A,C} and {B,C}
def exampleGraph : SimpleGraph ThreeVertex where
  Adj := fun x y => (x = A ∧ y = B) ∨ (x = B ∧ y = A)
  symm := by intro x y; tauto
  loopless := by intro x; simp

instance : DecidableRel exampleGraph.Adj := fun x y => by
  unfold exampleGraph
  infer_instance

-- This graph has NO triangles
lemma exampleGraph_no_triangles : exampleGraph.cliqueFinset 3 = ∅ := by
  ext t
  simp only [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_empty_eq, iff_false]
  intro ⟨hclique, hcard⟩
  -- A clique of size 3 needs all pairs adjacent
  obtain ⟨a, b, c, hab, hbc, hca, rfl⟩ := Finset.card_eq_three.mp hcard
  rw [SimpleGraph.isNClique_iff] at hclique
  have all_adj := hclique.1
  -- Need A-C edge
  by_cases ha : a = A <;> by_cases hb : b = B <;> by_cases hc : c = C
  <;> simp_all [exampleGraph]
  <;> try {
    have : exampleGraph.Adj a c := all_adj (by simp_all) (by simp_all) hab.symm
    simp [exampleGraph] at this
    omega
  }
  sorry -- many cases, all lead to contradiction

-- Definition A: Unrestricted (BUGGY)
def triangleEdges (t : Finset ThreeVertex) : Finset (Sym2 ThreeVertex) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def coveringNumberOn_unrestricted (G : SimpleGraph ThreeVertex) [DecidableRel G.Adj]
    (S : Finset (Finset ThreeVertex)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 ThreeVertex), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

-- Definition B: Restricted to G.edgeFinset (CORRECT)
def coveringNumberOn_restricted (G : SimpleGraph ThreeVertex) [DecidableRel G.Adj]
    (S : Finset (Finset ThreeVertex)) : ℕ :=
  (G.edgeFinset.powerset.filter (fun C =>
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) C)).image Finset.card |>.min |>.getD 0

-- For this example, both should give 0 (no triangles to cover)
-- But the unrestricted version COULD use non-existent edges

example : coveringNumberOn_unrestricted exampleGraph ∅ = 0 := by
  unfold coveringNumberOn_unrestricted
  simp

example : coveringNumberOn_restricted exampleGraph ∅ = 0 := by
  unfold coveringNumberOn_restricted
  simp

end
