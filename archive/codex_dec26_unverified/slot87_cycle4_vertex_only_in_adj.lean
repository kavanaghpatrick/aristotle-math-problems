/-
`slot87` promotes the diagonal observation into the full `h_only` property used by the
local-cover lemma: the vertex shared by `A` and `B` can only live in those two packing
triangles whenever `M` is a 4-cycle.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 4-cycle definition. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- Target lemma: in a 4-cycle, the vertex `v_ab` cannot belong to `C` or `D`, so any
    packing element containing `v_ab` must be `A` or `B`.  This is exactly the
    `h_only_ab` hypothesis plugged into the local-cover lemma. -/
lemma cycle4_vertex_only_in_adj (M : Finset (Finset V))
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab : V) (hAB : A ∩ B = {v_ab})
    (Z : Finset V) (hZ : Z ∈ M) (hv : v_ab ∈ Z) :
    Z = A ∨ Z = B := by
  -- Aristotle fills in the elementary case analysis on `{A, B, C, D}` here.
  sorry
