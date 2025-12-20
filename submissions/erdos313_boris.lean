import Mathlib

open Nat Finset

def erdos_313_solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

theorem erdos_313_conjecture : erdos_313_solutions.Infinite := by
  sorry
