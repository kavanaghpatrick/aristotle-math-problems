/-
Erdos Problem #1094 - Binomial Coefficient Prime Factors
OPEN: Only finitely many exceptions to minFac(C(n,k)) <= max(n/k, k)

ZERO custom definitions - uses ONLY Mathlib:
- Nat.choose (binomial coefficient)
- Nat.minFac (least prime factor)
- Set.Finite
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos1094

/-- OPEN: There are only finitely many pairs (n,k) with n >= 2k
    for which the least prime factor of C(n,k) exceeds max(n/k, k).

    EXACT statement from FormalConjectures - NO custom definitions. -/
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  sorry

/-- Test: For small values, the bound holds.
    C(4,2) = 6 has minFac = 2, and max(4/2, 2) = 2, so 2 <= 2. -/
theorem test_4_2 : ¬((4, 2) ∈ {(n, k) : ℕ × ℕ | 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}) := by
  simp only [Set.mem_setOf_eq, not_and, not_lt]
  intro _
  native_decide

/-- Test: C(6,3) = 20 has minFac = 2, max(6/3, 3) = 3, so 2 <= 3. -/
theorem test_6_3 : ¬((6, 3) ∈ {(n, k) : ℕ × ℕ | 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}) := by
  simp only [Set.mem_setOf_eq, not_and, not_lt]
  intro _
  native_decide

end Erdos1094
