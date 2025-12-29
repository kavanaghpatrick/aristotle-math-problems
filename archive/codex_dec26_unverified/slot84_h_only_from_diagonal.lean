/-
`slot84` records the simple but heavily used observation that the diagonals of the
cycle-of-four configuration are empty, hence each shared vertex only belongs to its two
adjacent triangles.  Aristotle can reuse this lemma whenever a `local_cover_le_2`
application demands the `h_only` hypothesis.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restating the definition keeps the file standalone. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- Target lemma: the shared vertex `v_ab` of `A` and `B` is missing from `C` and `D`
    because of the diagonal constraints.  This is precisely the property named
    `h_only_ab` in the main tau proof. -/
lemma h_only_from_diagonal {A B C D : Finset V}
    {v_ab : V} (hAB : A ∩ B = {v_ab})
    (hAC : (A ∩ C).card = 0) (hBD : (B ∩ D).card = 0) :
    v_ab ∉ C ∧ v_ab ∉ D := by
  classical
  have hvAB : v_ab ∈ A ∩ B := by
    simpa [hAB]
  have hvA : v_ab ∈ A := (Finset.mem_inter.mp hvAB).1
  have hvB : v_ab ∈ B := (Finset.mem_inter.mp hvAB).2
  have hACempty : A ∩ C = (∅ : Finset V) := Finset.card_eq_zero.mp hAC
  have hBDempty : B ∩ D = (∅ : Finset V) := Finset.card_eq_zero.mp hBD
  constructor
  · intro hvC
    have : v_ab ∈ A ∩ C := Finset.mem_inter.mpr ⟨hvA, hvC⟩
    simpa [hACempty] using this
  · intro hvD
    have : v_ab ∈ B ∩ D := Finset.mem_inter.mpr ⟨hvB, hvD⟩
    simpa [hBDempty] using this
