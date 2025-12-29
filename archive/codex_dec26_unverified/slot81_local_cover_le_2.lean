/-
`slot81` isolates the local covering lemma.  Aristotle can focus solely on the
`local_cover_le_2` argument without the rest of the cycle-of-four infrastructure.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangle packings are subsets of `cliqueFinset 3` with pairwise intersections of size ≤ 1. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- Maximum packing number, defined by simple enumeration. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G)
    |>.image Finset.card |>.max |>.getD 0

/-- `M` is maximal when it is a triangle packing whose size hits the packing number. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- All edges from packing triangles that touch the vertex `v`. -/
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- Target lemma: whenever a vertex sits on exactly two packing triangles `A` and `B`,
    there exists a local edge cover of size ≤ 2 that hits every supported triangle
    containing that vertex.  This is the key combinatorial fact exploited four times in
    the cycle-of-four proof, and Aristotle supplies the proof of this statement. -/
lemma local_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ M_edges_at G M v ∧
    ∀ t ∈ G.cliqueFinset 3, v ∈ t →
      (∃ e ∈ M_edges_at G M v, e ∈ t.sym2) →
      (∃ e ∈ E', e ∈ t.sym2) := by
  -- Proof imported from slot73 in the final submission; Aristotle fills this gap.
  sorry
