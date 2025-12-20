/-
Erdos Problem #141 - Consecutive Primes in Arithmetic Progression
OPEN: Are there k consecutive primes in AP for all k >= 3?

Original problem (erdosproblems.com/141):
"Let k ≥ 3. Are there k consecutive primes in arithmetic progression?"

FIX: Definitions at TOP LEVEL to avoid namespace scoping issues.
-/

import Mathlib

set_option maxHeartbeats 400000

/-- The predicate that a set s consists of l consecutive primes.
    A set of l consecutive primes starting from the a-th prime. -/
def IsPrimeProgressionOfLength (s : Set ℕ) (l : ℕ∞) : Prop :=
    ∃ a, ENat.card s = l ∧ s = {(a + n).nth Nat.Prime | (n : ℕ) (_ : n < l)}

/-- A set is an arithmetic progression of length l with first term a and step d. -/
def IsAPOfLengthWith (s : Set ℕ) (l : ℕ) (a d : ℕ) : Prop :=
  s = {a + d * i | (i : ℕ) (_ : i < l)}

/-- A set is an arithmetic progression of some length. -/
def IsAPOfLength (s : Set ℕ) (l : ℕ) : Prop :=
  ∃ a d, IsAPOfLengthWith s l a d

/-- The predicate that a set s is both an AP of length l and
    a progression of l consecutive primes. -/
def IsAPAndPrimeProgressionOfLength (s : Set ℕ) (l : ℕ) :=
   IsAPOfLength s l ∧ IsPrimeProgressionOfLength s l

/-- The set of arithmetic progressions of consecutive primes of length k. -/
def consecutivePrimeArithmeticProgressions (k : ℕ) : Set (Set ℕ) :=
  {s | IsAPAndPrimeProgressionOfLength s k}

/-- OPEN: Let k >= 3. Are there k consecutive primes in arithmetic progression?

    Green-Tao proved arbitrary long APs of primes exist, but not necessarily
    consecutive. Verified for k ≤ 10. Open for k = 11 and beyond. -/
theorem erdos_141 : (∀ k ≥ 3, ∃ (s : Set ℕ), IsAPAndPrimeProgressionOfLength s k)
    ↔ sorry := by
  sorry

/-- OPEN: Are there 11 consecutive primes in arithmetic progression? -/
theorem erdos_141_eleven : (∃ (s : Set ℕ), IsAPAndPrimeProgressionOfLength s 11)
    ↔ sorry := by
  sorry

/-- OPEN: Are there infinitely many 3-term APs of consecutive primes? -/
theorem erdos_141_infinite_three :
    (consecutivePrimeArithmeticProgressions 3).Infinite ↔ sorry := by
  sorry

/-- SOLVED: The existence has been verified for k <= 10. -/
theorem erdos_141_first_cases :
    (∀ k ≥ 3, k ≤ 10 → ∃ (s : Set ℕ), IsAPAndPrimeProgressionOfLength s k) := by
  sorry
