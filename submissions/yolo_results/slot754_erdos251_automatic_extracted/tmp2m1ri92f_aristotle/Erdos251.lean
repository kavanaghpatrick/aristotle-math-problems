/-
Erdős Problem 251: Irrationality of Σ p_n / 2^n

Erdős conjectured (1988) that Σ p_n^k / 2^n is irrational for k = 1, 2, 3.
The k = 1 case (this file) remains an open problem as of 2026.

This file proves:
  - A Chebyshev-type lower bound on the prime counting function
  - Summability of the series
  - The main irrationality statement is left as `sorry` (open conjecture)
-/

import Mathlib

set_option maxHeartbeats 800000

open scoped BigOperators Nat.Prime

open Nat Finset

noncomputable section

-- ============================================================================
-- Part 1: Chebyshev-type lower bound on π(x) via central binomial coefficient
-- ============================================================================

/-- C(2n, n) ≤ (2n)^{π(2n)} for n ≥ 1. -/
theorem centralBinom_le_pow_primeCounting (n : ℕ) (hn : 1 ≤ n) :
    n.centralBinom ≤ (2 * n) ^ (π (2 * n)) := by
  have h_def : Nat.centralBinom n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (2 * n + 1)), p ^ (Nat.factorization (Nat.centralBinom n) p) := by
    conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.centralBinom_pos n ) ) ] ;
    rw [ Finsupp.prod_of_support_subset ] <;> norm_num [ Nat.centralBinom ];
    exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_of_not_lt fun h => absurd ( Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors hp ) ( Nat.choose_mul_factorial_mul_factorial ( show n ≤ 2 * n by linarith ) ▸ dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _ ) ) ( mt ( Nat.Prime.dvd_factorial ( Nat.prime_of_mem_primeFactors hp ) |>.1 ) ( by linarith ) ) ) ), Nat.prime_of_mem_primeFactors hp ⟩ ;
  have h_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * n + 1)), p ^ (Nat.factorization (Nat.centralBinom n) p) ≤ 2 * n := by
    intro p hp; have := @Nat.pow_factorization_choose_le p ( 2 * n ) n ( by positivity ) ; ( norm_num at * ; );
    convert this using 1;
  refine h_def.le.trans ( le_trans ( Finset.prod_le_prod' h_bound ) ?_ );
  norm_num [ Nat.primeCounting, Nat.count_eq_card_filter_range ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ]

/-- From 4^n ≤ 2n * C(2n,n) and C(2n,n) ≤ (2n)^{π(2n)}, we get
4^n ≤ (2n)^{π(2n)+1}. -/
theorem four_pow_le_pow_primeCounting_succ (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ (2 * n) ^ (π (2 * n) + 1) := by
  have h1 : 4 ^ n ≤ 2 * n * (2 * n) ^ (π (2 * n)) := by
    exact le_trans ( Nat.four_pow_le_two_mul_self_mul_centralBinom n hn ) ( Nat.mul_le_mul_left _ ( centralBinom_le_pow_primeCounting n hn ) );
  convert h1 using 1 ; ring

/-
============================================================================
Part 2: n² < 2^(n-1) for n ≥ 7 (used to derive prime counting lower bound)
============================================================================

For n ≥ 7, n² < 2^(n-1). Proved by induction:
Base: 49 < 64. Step: if n² < 2^(n-1), then (n+1)² < 2n² < 2^n.
-/
theorem sq_lt_two_pow_pred (n : ℕ) (hn : 7 ≤ n) : n ^ 2 < 2 ^ (n - 1) := by
  induction' hn with k hk <;> norm_num [ Nat.pow_succ' ] at * ; rcases k with ( _ | _ | _ | _ | _ | _ | _ | k ) <;> norm_num [ Nat.pow_succ' ] at * ; nlinarith;

/-
For n ≥ 7, n^{2(n+1)} < 2^{n²-1}.
From sq_lt_two_pow_pred: n² < 2^{n-1}, so (n²)^{n+1} < (2^{n-1})^{n+1} = 2^{(n-1)(n+1)} = 2^{n²-1}.
-/
theorem pow_lt_two_pow_sq_pred (n : ℕ) (hn : 7 ≤ n) :
    n ^ (2 * (n + 1)) < 2 ^ (n ^ 2 - 1) := by
  convert Nat.pow_lt_pow_left ( sq_lt_two_pow_pred n hn ) ( by positivity : n + 1 ≠ 0 ) using 1 ; ring_nf; (
  rw [ ← pow_mul, mul_comm, ← Nat.sq_sub_sq ]);

/-
============================================================================
Part 3: π(n²) ≥ n + 1 for n ≥ 7 (Chebyshev lower bound on primes ≤ n²)
============================================================================

For n ≥ 7, π(n²) ≥ n + 1. Proof by contradiction: if π(n²) ≤ n, then
4^⌊n²/2⌋ ≤ (n²)^{π(n²)+1} ≤ (n²)^{n+1} = n^{2(n+1)},
but n^{2(n+1)} < 2^{n²-1} ≤ 4^⌊n²/2⌋, contradiction.
-/
theorem primeCounting_sq_ge (n : ℕ) (hn : 7 ≤ n) : n + 1 ≤ π (n ^ 2) := by
  -- By four_pow_le_pow_primeCounting_succ with m = n^2 / 2: 4^m ≤ (2*m)^{π(2*m)+1}
  have h_four_pow : 4 ^ (n ^ 2 / 2) ≤ (n ^ 2) ^ (Nat.primeCounting (n ^ 2) + 1) := by
    have h_four_pow : 4 ^ (n ^ 2 / 2) ≤ (2 * (n ^ 2 / 2)) ^ (Nat.primeCounting (2 * (n ^ 2 / 2)) + 1) := by
      convert four_pow_le_pow_primeCounting_succ ( n ^ 2 / 2 ) ( Nat.div_pos ( by nlinarith ) zero_lt_two ) using 1;
    refine le_trans h_four_pow ?_;
    gcongr;
    · nlinarith;
    · linarith [ Nat.div_mul_le_self ( n ^ 2 ) 2 ];
    · exact Nat.monotone_primeCounting <| Nat.mul_div_le _ _;
  by_cases h_contra : Nat.primeCounting (n ^ 2) ≤ n;
  · -- But by pow_lt_two_pow_sq_pred: n^{2*(n+1)} < 2^{n²-1}
    have h_pow_lt : n ^ (2 * (n + 1)) < 2 ^ (n ^ 2 - 1) := by
      exact pow_lt_two_pow_sq_pred n hn;
    -- And 2^{n²-1} ≤ 2^{2*m} = 4^m (since 2*m ≥ n²-1 when n² is odd, and 2*m = n² when n² is even, both giving n²-1 ≤ 2*m)
    have h_two_pow_le : 2 ^ (n ^ 2 - 1) ≤ 4 ^ (n ^ 2 / 2) := by
      rw [ show ( 4 : ℕ ) = 2 ^ 2 by norm_num, ← pow_mul ] ; exact pow_le_pow_right₀ ( by norm_num ) ( by omega ) ;
    exact absurd h_pow_lt ( by rw [ pow_mul ] ; exact not_lt_of_ge ( le_trans h_two_pow_le <| h_four_pow.trans <| Nat.pow_le_pow_right ( by positivity ) <| by linarith ) );
  · linarith

/-
============================================================================
Part 4: The n-th prime ≤ n² for n ≥ 6
============================================================================

For n ≥ 6, the n-th prime ≤ n². For n = 6 by computation, for n ≥ 7 from
primeCounting_sq_ge (π(n²) ≥ n+1 means there are ≥ n+1 primes ≤ n²,
so the n-th prime (0-indexed) ≤ n²).
-/
theorem nthPrime_le_sq (n : ℕ) (hn : 6 ≤ n) :
    Nat.nth Nat.Prime n ≤ n ^ 2 := by
  -- By primeCounting_sq_ge, π(n²) ≥ n + 1. This means there are at least n+1 primes ≤ n².
  have h_prime_count : Nat.count Nat.Prime (n ^ 2 + 1) ≥ n + 1 := by
    by_cases hn7 : n ≥ 7;
    · exact primeCounting_sq_ge n hn7;
    · interval_cases n ; native_decide;
  refine' Nat.le_of_lt_succ ( Nat.nth_lt_of_lt_count _ );
  linarith

/-
============================================================================
Part 5: Summability
============================================================================

The general term p_n / 2^n is summable. For n ≥ 6, the terms are bounded
by n^2/2^n, which is summable by summable_pow_mul_geometric_of_norm_lt_one.
-/
theorem summable_nthPrime_div_two_pow :
    Summable (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / 2 ^ n) := by
  -- For n ≥ 6, we have p_n ≤ n^2.
  have h_bound : ∀ n ≥ 6, (nth Nat.Prime n : ℝ) ≤ n^2 := by
    exact fun n hn => mod_cast nthPrime_le_sq n hn;
  -- Therefore, for n ≥ 6, we have (nth Nat.Prime n : ℝ) / 2^n ≤ n^2 / 2^n.
  have h_le : ∀ n ≥ 6, (nth Nat.Prime n : ℝ) / 2^n ≤ n^2 / 2^n := by
    exact fun n hn => by gcongr ; exact h_bound n hn;
  -- The series $\sum_{n=6}^{\infty} \frac{n^2}{2^n}$ is a geometric series with common ratio $1/2$.
  have h_geo_series : Summable (fun n : ℕ => (n^2 : ℝ) / 2^n) := by
    convert summable_pow_mul_geometric_of_norm_lt_one 2 ( show ‖ ( 1 / 2 : ℝ )‖ < 1 by norm_num ) using 2 ; norm_num ; ring_nf
    norm_num;
  rw [ ← summable_nat_add_iff 6 ] at *;
  exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => h_le _ ( by linarith ) ) h_geo_series

-- ============================================================================
-- Part 6: Main theorem (OPEN CONJECTURE)
-- ============================================================================

/-- **Erdős Problem 251**: The sum Σ p_n / 2^n is irrational.
This is an open conjecture (Erdős 1988). -/
theorem erdos_251 : Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / 2 ^ n) := by
  sorry

end