/-
Erdős Problem #730 - Binomial coefficients sharing prime divisors
OPEN: Are there infinitely many pairs n < m where C(2n,n) and C(2m,m) have the same prime factors?

Based on FormalConjectures/ErdosProblems/730.lean

Known examples: (87,88), (607,608) - all known cases have m = n+1
AlphaProof found non-consecutive pair: (10003, 10005)
-/

import Mathlib

set_option maxHeartbeats 400000

/-- The set of pairs (n,m) with n < m where C(2n,n) and C(2m,m) have the same prime factors -/
abbrev centralBinomPairs :=
  {(n, m) : ℕ × ℕ | n < m ∧ n.centralBinom.primeFactors = m.centralBinom.primeFactors}

/-- OPEN: Are there infinitely many such pairs? -/
theorem erdos_730 : centralBinomPairs.Infinite ↔ sorry := by
  sorry

/-- Known examples: (87,88) and (607,608) are in the set.
    Note: These are too large to compute directly with native_decide. -/
theorem erdos_730_explicit_pairs :
    {(87, 88), (607, 608)} ⊆ centralBinomPairs := by
  sorry

/-- All central binomial coefficients are even for n > 0 -/
theorem erdos_730_two_divides (n : ℕ) (hn : 0 < n) : 2 ∣ n.centralBinom := by
  exact Nat.two_dvd_centralBinom n hn

/-- There exist non-consecutive pairs (n, m) with m ≠ n + 1.
    Found by AlphaProof: (10003, 10005) -/
theorem erdos_730_non_consecutive :
    ∃ (n m : ℕ), (n, m) ∈ centralBinomPairs ∧ m ≠ n + 1 := by
  -- The proof involves showing 10003.centralBinom and 10005.centralBinom share prime factors
  -- This requires advanced techniques beyond native_decide due to the size of the numbers
  dsimp [centralBinomPairs]
  use 10003
  use 10005
  norm_num [Finset.ext_iff, Nat.choose_eq_zero_iff, Nat.centralBinom]
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  intro p hp
  constructor
  all_goals exact fun h' => or_self_iff.1 (hp.dvd_mul.1 (
    h'.trans (by refine' of_decide_eq_true (by constructor : _ = ↑_))))

/-- Small example: C(2,1) = 2 and C(4,2) = 6 don't share prime factors (counterexample to show
    not all pairs work) -/
theorem erdos_730_small_counterexample :
    (1, 2) ∉ centralBinomPairs := by
  simp only [centralBinomPairs, Set.mem_setOf_eq, not_and]
  intro _
  -- 1.centralBinom = C(2,1) = 2, primeFactors = {2}
  -- 2.centralBinom = C(4,2) = 6, primeFactors = {2, 3}
  native_decide
