import Mathlib

/-!
# Erdős Problem 398 — Brocard's Problem

The only solutions to n! + 1 = m² are n = 4, 5, 7.

This is an **open problem** in number theory, first posed by Brocard in 1876 and
later highlighted by Erdős. It has been verified computationally up to n = 10⁹
but no proof is known.

We prove the easy direction ({4, 5, 7} are indeed solutions) and leave the
hard direction (no other solutions exist) as `sorry` since it is an open conjecture.
-/

open Nat in
/-- The easy direction: 4, 5, and 7 are all Brocard numbers.
  4! + 1 = 25 = 5², 5! + 1 = 121 = 11², 7! + 1 = 5041 = 71². -/
theorem erdos_398_easy :
    {4, 5, 7} ⊆ {n : ℕ | ∃ m : ℕ, n.factorial + 1 = m ^ 2} := by
  norm_num [Set.insert_subset_iff]
  exact ⟨⟨5, rfl⟩, ⟨11, rfl⟩, ⟨71, rfl⟩⟩

open Nat in
/-- The hard direction (OPEN CONJECTURE): there are no Brocard numbers beyond 7.
This is Brocard's problem, open since 1876. Verified computationally to n = 10⁹. -/
theorem erdos_398_hard :
    {n : ℕ | ∃ m : ℕ, n.factorial + 1 = m ^ 2} ⊆ {4, 5, 7} := by
  sorry

open Nat in
/-- **Brocard's Problem (Erdős 398)**: The only solutions to n! + 1 = m² are n = 4, 5, 7.
This is an open conjecture. The proof of the forward inclusion (`erdos_398_easy`) is
complete; the reverse inclusion (`erdos_398_hard`, that no other solutions exist) remains
open and is marked `sorry`. -/
theorem erdos_398 :
    {n : ℕ | ∃ m : ℕ, n.factorial + 1 = m ^ 2} = {4, 5, 7} := by
  exact Set.eq_of_subset_of_subset erdos_398_hard erdos_398_easy
