/-
Erdős Problem #1052 - Unitary Perfect Numbers
Target: Prove that all unitary perfect numbers are even.

This is a KNOWN result - no odd unitary perfect numbers exist.
The formalization marks this as "research solved" with sorry.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators

noncomputable section

namespace Erdos1052

/-- A proper unitary divisor of n is a divisor d of n
such that d is coprime to n/d, and d < n. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- A number n > 0 is a unitary perfect number if it is the sum of its proper unitary divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- All unitary perfect numbers are even.

Proof sketch: If n is odd, then all its divisors are odd.
For any divisor d of n with gcd(d, n/d) = 1, both d and n/d are odd.
The sum of proper unitary divisors would be a sum of odd numbers.
For n to equal this sum, we need specific parity constraints that fail for odd n.
-/
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  sorry

/-- 6 is a unitary perfect number. -/
theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- 60 is a unitary perfect number. -/
theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- 90 is a unitary perfect number. -/
theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

end Erdos1052
