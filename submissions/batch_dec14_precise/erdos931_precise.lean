/-
Erdős Problem #931 - Products sharing same prime factors
OPEN: Are there only finitely many pairs where products of consecutive integers share the same prime factors?

Based on FormalConjectures/ErdosProblems/931.lean

Given k₁ ≥ k₂ ≥ 3, are there only finitely many n₂ ≥ n₁+k₁ such that
∏(n₁+i for i=1..k₁) and ∏(n₂+j for j=1..k₂) have the same prime factors?

AlphaProof found counterexample: 10! and 14·15·16 both have prime factors {2,3,5,7}
(k₁=10, k₂=3, n₁=0, n₂=13)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

/-- Product of consecutive integers from n+1 to n+k -/
def consecutiveProduct (n k : ℕ) : ℕ := ∏ i ∈ Icc 1 k, (n + i)

/-- OPEN: For k₁ ≥ k₂ ≥ 3, are there only finitely many pairs (n₁, n₂)
    with n₁ + k₁ ≤ n₂ where the products share the same prime factors? -/
theorem erdos_931 : (∀ k₁ k₂ : ℕ, k₂ ≥ 3 → k₂ ≤ k₁ →
    { (n₁, n₂) | n₁ + k₁ ≤ n₂ ∧
      (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors }.Finite) ↔ sorry := by
  sorry

/-- Variant: Erdős thought perhaps n₂ > 2(n₁ + k₁) always holds (with finitely many exceptions) -/
theorem erdos_931_additional_condition : (∀ k₁ k₂ : ℕ, k₂ ≥ 3 → k₂ ≤ k₁ →
    {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
      (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors}.Finite) ↔ sorry := by
  sorry

/-- AlphaProof counterexample: k₁=10, k₂=3, n₁=0, n₂=13
    10! = 3628800 has prime factors {2,3,5,7}
    14·15·16 = 3360 has prime factors {2,3,5,7}

    This shows counterexamples to the stronger condition exist. -/
theorem erdos_931_counterexample :
    ∃ (k₁ k₂ : ℕ), k₂ ≤ k₁ ∧ 3 ≤ k₂ ∧
    {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
      (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors}.Nonempty := by
  use 10, 3
  constructor; norm_num
  constructor; norm_num
  use (0, 13)
  simp only [Set.mem_setOf_eq, Icc_self, prod_singleton]
  constructor; norm_num
  constructor; norm_num
  -- 10! = 2^8 * 3^4 * 5^2 * 7, prime factors = {2,3,5,7}
  -- 14*15*16 = 2*7 * 3*5 * 2^4 = 2^5 * 3 * 5 * 7, prime factors = {2,3,5,7}
  norm_num [Finset.prod_Icc_succ_top]
  norm_num +decide [Nat.primeFactors, Nat.primeFactorsList]

/-- Test: consecutiveProduct 0 10 = 10! = 3628800 -/
theorem test_factorial_10 : consecutiveProduct 0 10 = 3628800 := by
  unfold consecutiveProduct
  native_decide

/-- Test: consecutiveProduct 13 3 = 14·15·16 = 3360 -/
theorem test_product_14_15_16 : consecutiveProduct 13 3 = 3360 := by
  unfold consecutiveProduct
  native_decide

/-- Test: Both products have the same prime factors {2,3,5,7} -/
theorem test_same_prime_factors :
    (consecutiveProduct 0 10).primeFactors = (consecutiveProduct 13 3).primeFactors := by
  unfold consecutiveProduct
  native_decide
