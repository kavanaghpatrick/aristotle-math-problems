/-
Erdős Problem #1052 - Unitary Perfect Numbers
OPEN: Are there only finitely many unitary perfect numbers?

Known: 5 examples exist (6, 60, 90, 87360, 146361946186458562560000)
Known: All are even (no odd unitary perfect numbers exist)

This is a classic open problem in number theory.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos1052

/-- Proper unitary divisors of n: divisors d with gcd(d, n/d) = 1 and d < n -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- n is unitary perfect if it equals sum of proper unitary divisors -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- OPEN: Are there only finitely many unitary perfect numbers? -/
theorem erdos_1052 : Set.Finite {n | IsUnitaryPerfect n} ↔ sorry := by
  sorry

/-- Test: 6 is unitary perfect -/
theorem test_6 : IsUnitaryPerfect 6 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- Test: 60 is unitary perfect -/
theorem test_60 : IsUnitaryPerfect 60 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- Known theorem: All unitary perfect numbers are even -/
theorem all_even (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  sorry

end Erdos1052
