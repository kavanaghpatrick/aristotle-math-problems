/-
Erdos Problem #141 - Consecutive Primes in Arithmetic Progression
OPEN: Are there k consecutive primes in AP for all k >= 3?

SELF-CONTAINED definitions matching FormalConjectures exactly.
Uses ENat.card, Nat.nth, Nat.Prime from Mathlib.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos141

/-- The predicate that a set s consists of l consecutive primes.
    EXACT definition from FormalConjectures. -/
def Set.IsPrimeProgressionOfLength (s : Set ℕ) (l : ℕ∞) : Prop :=
    ∃ a, ENat.card s = l ∧ s = {(a + n).nth Nat.Prime | (n : ℕ) (_ : n < l)}

/-- A set is an arithmetic progression of length l with first term a and step d. -/
def Set.IsAPOfLengthWith (s : Set ℕ) (l : ℕ) (a d : ℕ) : Prop :=
  s = {a + d * i | (i : ℕ) (_ : i < l)}

/-- A set is an arithmetic progression of some length. -/
def Set.IsAPOfLength (s : Set ℕ) (l : ℕ) : Prop :=
  ∃ a d, s.IsAPOfLengthWith l a d

/-- The predicate that a set s is both an AP of length l and
    a progression of l consecutive primes.
    EXACT definition from FormalConjectures. -/
def Set.IsAPAndPrimeProgressionOfLength (s : Set ℕ) (l : ℕ) :=
   s.IsAPOfLength l ∧ s.IsPrimeProgressionOfLength l

/-- The set of arithmetic progressions of consecutive primes of length k.
    EXACT definition from FormalConjectures. -/
def consecutivePrimeArithmeticProgressions (k : ℕ) : Set (Set ℕ) :=
  {s | s.IsAPAndPrimeProgressionOfLength k}

/-- OPEN: Let k >= 3. Are there k consecutive primes in arithmetic progression? -/
theorem erdos_141 : (∀ k ≥ 3, ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength k)
    ↔ sorry := by
  sorry

/-- OPEN: Are there 11 consecutive primes in arithmetic progression? -/
theorem erdos_141_eleven : (∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength 11)
    ↔ sorry := by
  sorry

/-- OPEN: Are there infinitely many 3-term APs of consecutive primes? -/
theorem erdos_141_infinite_three :
    (consecutivePrimeArithmeticProgressions 3).Infinite ↔ sorry := by
  sorry

/-- OPEN: For k >= 3, are there infinitely many k-term APs of consecutive primes? -/
theorem erdos_141_infinite_general (k : ℕ) (hk : k ≥ 3) :
    (consecutivePrimeArithmeticProgressions k).Infinite ↔ sorry := by
  sorry

/-- SOLVED: The existence has been verified for k <= 10. -/
theorem erdos_141_first_cases :
    (∀ k ≥ 3, k ≤ 10 → ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength k) := by
  sorry

/-- Test: {3, 5, 7} are 3 consecutive primes in AP. -/
theorem test_3_5_7 : ({3, 5, 7} : Set ℕ).IsAPAndPrimeProgressionOfLength 3 := by
  constructor
  · use 3, 2
    unfold Set.IsAPOfLengthWith
    constructor
    · aesop
    · ext x; simp [Set.mem_insert_iff]; omega
  · use 1
    constructor
    · simp
    · ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨n, hn, rfl⟩
        interval_cases n <;> simp [Nat.nth]
      · intro hx
        rcases hx with rfl | rfl | rfl
        all_goals { use ?_; constructor; omega; simp [Nat.nth] }
        · exact 0
        · exact 1
        · exact 2

end Erdos141
