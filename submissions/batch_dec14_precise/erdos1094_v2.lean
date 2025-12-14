/-
Erdos Problem #1094 - Binomial Coefficient Prime Factors
OPEN: Only finitely many exceptions to minFac(C(n,k)) <= max(n/k, k)

Original problem (erdosproblems.com/1094):
"For all n ≥ 2k the least prime factor of C(n,k) is ≤ max(n/k, k),
with only finitely many exceptions."

Known exceptions include C(7,3), C(13,4), C(62,6) (14 total known).

FIX: Add k ≥ 1 constraint. The original problem implicitly requires k ≥ 1:
- Binomial coefficients C(n,0) = 1 are trivial
- The bound "n/k" is undefined for k=0
- Without k ≥ 1, infinitely many (n,0) pairs would be "exceptions"
-/

import Mathlib

set_option maxHeartbeats 400000

/-- OPEN: There are only finitely many pairs (n,k) with k ≥ 1 and n ≥ 2k
    for which the least prime factor of C(n,k) exceeds max(n/k, k).

    The k ≥ 1 constraint matches the original problem's intent:
    - Binomial coefficients are meaningful for k ≥ 1
    - The bound n/k requires k > 0
    - 14 exceptions are known (e.g., C(7,3), C(13,4), C(62,6)) -/
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 1 ≤ k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite
    ↔ sorry := by
  sorry

/-- Variant: The stronger conjecture with bound max(n/k, √k) -/
theorem erdos_1094_stronger :
    {(n, k) : ℕ × ℕ | 1 ≤ k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) (Nat.sqrt k)}.Finite
    ↔ sorry := by
  sorry

/-- Test: For small values, the bound holds.
    C(4,2) = 6 has minFac = 2, and max(4/2, 2) = 2, so 2 <= 2. -/
theorem test_4_2 : ¬((4, 2) ∈ {(n, k) : ℕ × ℕ | 1 ≤ k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}) := by
  simp only [Set.mem_setOf_eq, not_and, not_lt]
  intro _ _
  native_decide

/-- Test: C(6,3) = 20 has minFac = 2, max(6/3, 3) = 3, so 2 <= 3. -/
theorem test_6_3 : ¬((6, 3) ∈ {(n, k) : ℕ × ℕ | 1 ≤ k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}) := by
  simp only [Set.mem_setOf_eq, not_and, not_lt]
  intro _ _
  native_decide

/-- Known exception: C(7,3) = 35 has minFac = 5, max(7/3, 3) = max(2, 3) = 3, so 5 > 3. -/
theorem exception_7_3 : (7, 3) ∈ {(n, k) : ℕ × ℕ | 1 ≤ k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k} := by
  simp only [Set.mem_setOf_eq]
  native_decide
