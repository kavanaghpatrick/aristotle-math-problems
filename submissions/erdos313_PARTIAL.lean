/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6032415c-dbed-4ed1-92dc-cf6c5075695b
-/

/-
Erdos Problem #313 - Primary Pseudoperfect Numbers
OPEN: Are there infinitely many primary pseudoperfect numbers?

SELF-CONTAINED definitions matching FormalConjectures exactly.
Uses only Mathlib: Finset, Nat.Prime, Rational arithmetic.
-/

import Mathlib


set_option maxHeartbeats 400000

namespace Erdos313

/-- Solutions to Erdos 313: pairs (m, P) where m >= 2 and P is a set of
    distinct primes such that sum of 1/p for p in P equals 1 - 1/m.
    EXACT definition from FormalConjectures. -/
def erdos_313_solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

/-- A primary pseudoperfect number is the denominator m in a solution (m, P).
    EXACT definition from FormalConjectures. -/
def IsPrimaryPseudoperfect (n : ℕ) : Prop := ∃ P, (n, P) ∈ erdos_313_solutions

/- Aristotle took a wrong turn (reason code: 8). Please try again. -/
/-- OPEN: Are there infinitely many solutions (m, P)? -/
theorem erdos_313_conjecture : erdos_313_solutions.Infinite ↔ sorry := by
  sorry

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
/-- OPEN: Are there infinitely many primary pseudoperfect numbers? -/
theorem erdos_313_infinite :
    Set.Infinite {n | IsPrimaryPseudoperfect n} := by
  sorry

/-- Test: (6, {2, 3}) is a solution since 1/2 + 1/3 = 5/6 = 1 - 1/6. -/
theorem solution_6_2_3 : (6, {2, 3}) ∈ erdos_313_solutions := by
  simp only [erdos_313_solutions, Set.mem_setOf_eq]
  refine ⟨by norm_num, by simp, ?_, ?_⟩
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl <;> norm_num
  · norm_num

/-- Test: (42, {2, 3, 7}) is a solution since 1/2 + 1/3 + 1/7 = 41/42 = 1 - 1/42. -/
theorem solution_42_2_3_7 : (42, {2, 3, 7}) ∈ erdos_313_solutions := by
  simp only [erdos_313_solutions, Set.mem_setOf_eq]
  refine ⟨by norm_num, by simp, ?_, ?_⟩
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  · norm_num

/-- Test: 6 is a primary pseudoperfect number. -/
theorem isPrimaryPseudoperfect_6 : IsPrimaryPseudoperfect 6 := by
  exact ⟨{2, 3}, solution_6_2_3⟩

/-- Test: 42 is a primary pseudoperfect number. -/
theorem isPrimaryPseudoperfect_42 : IsPrimaryPseudoperfect 42 := by
  exact ⟨{2, 3, 7}, solution_42_2_3_7⟩

end Erdos313