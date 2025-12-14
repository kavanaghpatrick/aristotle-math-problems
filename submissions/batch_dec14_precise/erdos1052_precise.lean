/-
Erdős Problem #1052 - Unitary Perfect Numbers
OPEN: Are there only finitely many unitary perfect numbers?

SELF-CONTAINED definitions (same as FormalConjectures):
- properUnitaryDivisors: d | n with gcd(d, n/d) = 1 and d < n
- IsUnitaryPerfect: sum of proper unitary divisors = n
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos1052

/-- Proper unitary divisors of n: divisors d of n such that
    gcd(d, n/d) = 1 and d < n.
    This is the EXACT definition from FormalConjectures. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- n is a unitary perfect number if the sum of its proper
    unitary divisors equals n, and n > 0.
    This is the EXACT definition from FormalConjectures. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- OPEN: Are there only finitely many unitary perfect numbers?

    Known facts:
    - 5 examples exist: 6, 60, 90, 87360, 146361946186458562560000
    - All are even (no odd unitary perfect numbers) -/
theorem erdos_1052 : Set.Finite {n | IsUnitaryPerfect n} ↔ sorry := by
  sorry

/-- SOLVED: All unitary perfect numbers are even. -/
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  sorry

/-- Test case: 6 is unitary perfect.
    Proper unitary divisors of 6: 1, 2, 3 (all coprime to their complement)
    1 + 2 + 3 = 6 ✓ -/
theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- Test case: 60 is unitary perfect. -/
theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- Test case: 90 is unitary perfect. -/
theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

end Erdos1052
