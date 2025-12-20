/-
Erdős Problem #1059 - Primes where p - k! is always composite
OPEN: Are there infinitely many such primes?

Uses ONLY Mathlib definitions:
- Nat.factorial
- Nat.Prime
- Nat.Composite
- Set.Infinite
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos1059

/-- A number is a factorial if it's in the range of factorial function.
    EXACT definition from FormalConjectures. -/
def IsFactorial (d : ℕ) : Prop := d ∈ Set.range Nat.factorial

/-- All factorials less than n. -/
def factorialsLessThanN (n : ℕ) : Set ℕ :=
  { d | d < n ∧ IsFactorial d }

/-- n has the property that p - k! is composite for all factorials k! < n.
    EXACT definition from FormalConjectures. -/
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ d ∈ factorialsLessThanN n, (n - d).Composite

/-- The set of primes with this property. -/
def SpecialPrimes : Set ℕ := {p | p.Prime ∧ AllFactorialSubtractionsComposite p}

/-- OPEN: Are there infinitely many primes p such that p - k! is
    composite for each k with 1 ≤ k! < p?

    Known examples: p = 101 and p = 211 -/
theorem erdos_1059 : SpecialPrimes.Infinite ↔ sorry := by
  sorry

/-
Verification for p = 101:
Factorials less than 101: 1! = 1, 2! = 2, 3! = 6, 4! = 24 (since 5! = 120 > 101)
- 101 - 1 = 100 = 4 × 25 ✓ composite
- 101 - 2 = 99 = 9 × 11 ✓ composite
- 101 - 6 = 95 = 5 × 19 ✓ composite
- 101 - 24 = 77 = 7 × 11 ✓ composite
-/

end Erdos1059
