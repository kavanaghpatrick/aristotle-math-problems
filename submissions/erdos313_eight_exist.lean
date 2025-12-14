/-
Erdős Problem #313 - Primary Pseudoperfect Numbers
Target: Prove there exist at least 8 primary pseudoperfect numbers.

A primary pseudoperfect number m satisfies:
  1/p₁ + 1/p₂ + ... + 1/pₖ = 1 - 1/m
for some distinct primes p₁ < p₂ < ... < pₖ.

Known examples (OEIS A054377):
1. m = 2: 1/2 = 1 - 1/2 (trivial, P = {2})
2. m = 6: 1/2 + 1/3 = 5/6 = 1 - 1/6
3. m = 42: 1/2 + 1/3 + 1/7 = 41/42 = 1 - 1/42
4. m = 1806: 1/2 + 1/3 + 1/7 + 1/43 = 1805/1806 = 1 - 1/1806
5. m = 47058: ...
6. m = 2214502422: ...
7. m = 52495396602: ...
8. m = 8490421583559688410706771261086: ...
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators

namespace Erdos313

/--
The set of all solutions (m, P) where m ≥ 2 and P is a finite set of distinct primes
such that ∑_{p ∈ P} 1/p = 1 - 1/m.
-/
def erdos_313_solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

/-- m = 2 with P = {2} is a solution: 1/2 = 1 - 1/2 -/
theorem solution_2 : (2, {2}) ∈ erdos_313_solutions := by
  simp [erdos_313_solutions]
  norm_num

/-- m = 6 with P = {2, 3} is a solution: 1/2 + 1/3 = 1 - 1/6 -/
theorem solution_6 : (6, {2, 3}) ∈ erdos_313_solutions := by
  norm_num [erdos_313_solutions]

/-- m = 42 with P = {2, 3, 7} is a solution: 1/2 + 1/3 + 1/7 = 1 - 1/42 -/
theorem solution_42 : (42, {2, 3, 7}) ∈ erdos_313_solutions := by
  norm_num [erdos_313_solutions]

/-- m = 1806 with P = {2, 3, 7, 43} is a solution -/
theorem solution_1806 : (1806, {2, 3, 7, 43}) ∈ erdos_313_solutions := by
  norm_num [erdos_313_solutions]

/-- An integer n is a primary pseudoperfect number if it is the m in some solution (m, P). -/
def IsPrimaryPseudoperfect (n : ℕ) : Prop := ∃ P, (n, P) ∈ erdos_313_solutions

/-- There are at least 8 primary pseudoperfect numbers. -/
theorem exists_at_least_eight_primary_pseudoperfect :
    8 ≤ (Set.encard {n | IsPrimaryPseudoperfect n}) := by
  sorry

end Erdos313
