/-
Erdős Problem #730 - Central Binomial Coefficients
Target: Prove that 2 divides C(2n, n) for all n > 0.

This is a CLASSIC textbook result with multiple proofs:
1. C(2n,n) = C(2n-1,n-1) + C(2n-1,n) and both terms are integers
2. 2 * C(2n,n) = C(2n+1,n) - C(2n-1,n-1) type identities
3. Direct: C(2n,n) = 2 * C(2n-1,n-1) * (2n)/(n) = 2 * (2n-1)!/(n!(n-1)!)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators

namespace Erdos730

/--
The central binomial coefficient C(2n, n) is always even for n > 0.

This follows from the identity:
  C(2n, n) = 2 * C(2n-1, n-1)
which holds because C(2n,n) = C(2n-1,n-1) + C(2n-1,n) and C(2n-1,n-1) = C(2n-1,n).
-/
theorem two_div_centralBinom (n : ℕ) (h : 0 < n) : 2 ∣ n.centralBinom := by
  sorry

/--
Alternative formulation: C(2n, n) is even for all n ≥ 1.
-/
theorem centralBinom_even (n : ℕ) (h : 1 ≤ n) : Even n.centralBinom := by
  rw [even_iff_two_dvd]
  exact two_div_centralBinom n h

/--
The set S of pairs (n,m) with n < m where C(2n,n) and C(2m,m)
have the same prime factors.
-/
abbrev S : Set (ℕ × ℕ) :=
  {(n, m) : ℕ × ℕ | n < m ∧ n.centralBinom.primeFactors = m.centralBinom.primeFactors}

/--
Example pairs where consecutive central binomial coefficients share prime factors.
(87, 88) and (607, 608) are known examples.
-/
theorem explicit_pairs : {(87, 88), (607, 608)} ⊆ S := by
  sorry

end Erdos730
