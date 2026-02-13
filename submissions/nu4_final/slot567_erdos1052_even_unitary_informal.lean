/-!
# Erdős Problem 1052: All unitary perfect numbers are even

A number n is unitary perfect if the sum of its proper unitary divisors equals n.
A unitary divisor d of n satisfies gcd(d, n/d) = 1.

PROVIDED SOLUTION:
We prove that no odd number can be unitary perfect.

Suppose n > 0 is odd and unitary perfect. Write n = p₁^a₁ · p₂^a₂ · ... · pₖ^aₖ
where each pᵢ is an odd prime and aᵢ ≥ 1.

Key facts about unitary divisors:
1. The unitary divisors of n are exactly the products of subsets of {p₁^a₁, ..., pₖ^aₖ}.
   There are 2^k total unitary divisors (including 1 and n).

2. The sum of ALL unitary divisors (the unitary sigma function) is:
   σ*(n) = (1 + p₁^a₁)(1 + p₂^a₂)···(1 + pₖ^aₖ)

3. The sum of proper unitary divisors = σ*(n) - n.

4. Unitary perfect means σ*(n) - n = n, equivalently σ*(n) = 2n.

Now for the parity argument:
- Since n is odd, each pᵢ is odd, so each pᵢ^aᵢ is odd.
- Therefore each factor (1 + pᵢ^aᵢ) is even (odd + 1 = even).
- So σ*(n) = (1 + p₁^a₁)···(1 + pₖ^aₖ) is divisible by 2^k.

But σ*(n) = 2n = 2 × (odd number), so σ*(n) is divisible by exactly 2¹.

This forces k ≤ 1. We handle both cases:

Case k = 0: Then n = 1. But σ*(1) = 1 ≠ 2 = 2·1. Contradiction.

Case k = 1: Then n = p^a for some odd prime p with a ≥ 1.
  σ*(n) = 1 + p^a = 1 + n.
  We need σ*(n) = 2n, so 1 + n = 2n, giving n = 1.
  But n = p^a ≥ p ≥ 3 > 1. Contradiction.

In both cases we reach a contradiction, so n must be even. QED.

Key Mathlib lemmas:
- `Nat.Coprime`: coprimality definition
- `Finset.sum`: summing over a finset
- `Nat.Prime.odd_of_ne_two`: odd primes
- `Nat.even_iff`: characterize even numbers
- `Finset.prod_pos`: positivity of products
- `Nat.Coprime.mul_dvd_of_dvd_of_dvd`: coprimality implies factored divisibility
-/

import Mathlib

namespace Erdos1052

def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- All unitary perfect numbers are even. -/
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  sorry

end Erdos1052
