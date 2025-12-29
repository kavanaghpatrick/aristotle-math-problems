/-
`slot88` provides a quantitative version of the local edge bookkeeping: if a vertex `v`
belongs to exactly two packing triangles, then `M_edges_at G M v` has size at most four.
This fact is repeatedly used while assembling a global cover of size ≤ 8.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Local edges incident to `v` coming from the packing triangles. -/
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- Target lemma: only two triangles contain `v`, so `M_edges_at` contributes at most two
    edges from each triangle. -/
lemma M_edges_at_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hvA : v ∈ A) (hvB : v ∈ B)
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    (M_edges_at G M v).card ≤ 4 := by
  -- Aristotle proves this simple counting statement.
  sorry
