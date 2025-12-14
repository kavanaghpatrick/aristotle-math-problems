/-
Erdős Problem #1059 - Primes where p - k! is always composite
OPEN: Are there infinitely many such primes?

Known examples: p = 101 and p = 211 satisfy this.
The question is whether infinitely many exist.

This is a pure number theory question with decidable test cases.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos1059

/-- n is a factorial -/
def IsFactorial (d : ℕ) : Prop := d ∈ Set.range Nat.factorial

/-- All factorial subtractions from n are composite -/
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ d, d < n → IsFactorial d → (n - d).Composite

/-- The set of primes with this property -/
def SpecialPrimes : Set ℕ := {p | p.Prime ∧ AllFactorialSubtractionsComposite p}

/-- OPEN: Are there infinitely many such primes? -/
theorem erdos_1059 : SpecialPrimes.Infinite ↔ sorry := by
  sorry

/-- p = 101 is such a prime (verified computationally) -/
-- The factorials less than 101 are: 1, 2, 6, 24
-- 101 - 1 = 100 = 4 × 25 (composite)
-- 101 - 2 = 99 = 9 × 11 (composite)
-- 101 - 6 = 95 = 5 × 19 (composite)
-- 101 - 24 = 77 = 7 × 11 (composite)

end Erdos1059
