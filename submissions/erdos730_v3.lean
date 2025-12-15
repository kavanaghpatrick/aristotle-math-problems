/-
Erdős Problem #730 - Central Binomial Coefficients Sharing Prime Divisors
FIXED VERSION - No abbrev conflicts

PROBLEM: Are there infinitely many pairs n < m where C(2n,n) and C(2m,m)
have the same prime factors?

KNOWN EXAMPLES: (87,88), (607,608)
-/

import Mathlib

set_option maxHeartbeats 400000

open Nat Finset

/-! ## Definitions -/

/-- The set of pairs (n,m) with n < m where C(2n,n) and C(2m,m) share prime factors -/
def CentralBinomPairs : Set (ℕ × ℕ) :=
  {p | p.1 < p.2 ∧ p.1.centralBinom.primeFactors = p.2.centralBinom.primeFactors}

/-- Whether n has a digit ≥ threshold in base p -/
def HasLargeDigit (n p threshold : ℕ) : Prop :=
  ∃ k, (n / p ^ k) % p ≥ threshold

/-! ## Kummer's Theorem -/

/-- Kummer's theorem for central binomial: p | C(2n,n) iff carry in n+n base p -/
lemma kummer_centralBinom (n p : ℕ) (hp : p.Prime) :
    p ∣ n.centralBinom ↔ HasLargeDigit n p ((p + 1) / 2) := by
  sorry

/-! ## Recurrence -/

/-- The recurrence relation -/
theorem centralBinom_recurrence (n : ℕ) :
    (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom := by
  sorry

/-! ## Verified Examples -/

/-- (87, 88) is a valid pair -/
theorem pair_87_88 : (87, 88) ∈ CentralBinomPairs := by
  simp only [CentralBinomPairs, Set.mem_setOf_eq]
  constructor
  · norm_num
  · native_decide

/-- (607, 608) is a valid pair -/
theorem pair_607_608 : (607, 608) ∈ CentralBinomPairs := by
  simp only [CentralBinomPairs, Set.mem_setOf_eq]
  constructor
  · norm_num
  · native_decide

/-- (1, 2) is NOT a valid pair -/
theorem not_pair_1_2 : (1, 2) ∉ CentralBinomPairs := by
  simp only [CentralBinomPairs, Set.mem_setOf_eq, not_and, not_lt]
  intro _
  native_decide

/-- (3, 4) is NOT a valid pair -/
theorem not_pair_3_4 : (3, 4) ∉ CentralBinomPairs := by
  simp only [CentralBinomPairs, Set.mem_setOf_eq, not_and, not_lt]
  intro _
  native_decide

/-! ## Basic Properties -/

/-- All central binomials for n > 0 are even -/
theorem two_divides_centralBinom (n : ℕ) (hn : n > 0) : 2 ∣ n.centralBinom :=
  Nat.two_dvd_centralBinom n hn

/-- 2 is in the prime factors for n > 0 -/
theorem two_in_primeFactors (n : ℕ) (hn : n > 0) :
    2 ∈ n.centralBinom.primeFactors := by
  rw [Nat.mem_primeFactors]
  exact ⟨Nat.two_dvd_centralBinom n hn, Nat.centralBinom_pos n⟩

/-! ## Main Conjecture -/

/-- MAIN CONJECTURE: Infinitely many pairs exist -/
theorem erdos_730 : CentralBinomPairs.Infinite := by
  sorry

/-! ## OEIS Connection -/

/-- A129515: values n where some m > n works -/
def A129515 : Set ℕ := {n | ∃ m, (n, m) ∈ CentralBinomPairs}

/-- Known elements -/
theorem known_A129515 : {87, 607} ⊆ A129515 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact ⟨88, pair_87_88⟩
  · exact ⟨608, pair_607_608⟩

end
