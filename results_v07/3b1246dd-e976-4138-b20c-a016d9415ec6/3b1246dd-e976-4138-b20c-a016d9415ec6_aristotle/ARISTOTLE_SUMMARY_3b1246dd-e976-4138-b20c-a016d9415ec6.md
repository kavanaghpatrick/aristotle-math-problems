# Summary of changes
## Erdős Problem 931 — Formalization Summary

**Status**: This is an **open problem** in number theory. The main theorem `erdos931` remains `sorry`'d, as expected.

### Formalization changes

The original statement used `Nat.factors` (sorted list of prime factors with multiplicity), which is not available in this version of Mathlib. I adapted it to use `Nat.primeFactors` (the `Finset` of prime divisors without multiplicity), which actually matches the original Erdős problem more faithfully — the problem asks about equal *sets* of prime factors (equal radicals), not equal factorizations.

### What was proved

The file `RequestProject/Erdos931.lean` contains:

1. **`consecProd_pos`** ✅: The product of consecutive integers is always positive.

2. **`primeFactors_bound`** ✅: If the prime factor sets of two consecutive products match and n₁ + k₁ ≤ n₂, then every prime factor of the second product is ≤ n₁ + k₁. (Key structural constraint.)

3. **`smooth_constraint`** ✅: Each element of {n₂+1, ..., n₂+k₂} must have all its prime factors ≤ n₁ + k₁. This means the second range consists of (n₁+k₁)-smooth numbers.

4. **`boundary_prime_bound`** ✅: In the boundary case n₂ = n₁ + k₁, any prime dividing both products must be ≤ k₁ + k₂ - 1. This follows from the divisibility argument: if p | (n₁+i+1) and p | (n₁+k₁+j+1), then p | (k₁+j-i) where 1 ≤ k₁+j-i ≤ k₁+k₂-1.

5. **`consecutive_smooth_finite`** (axiom): The S-unit equation theorem — for any bound B and k ≥ 2, there are finitely many runs of k consecutive B-smooth integers. This deep result (due to Størmer/Evertse/Baker) is not in Mathlib.

### Why the main theorem remains open

Computational evidence (checked up to n₁ = 200) suggests finitely many solutions — the largest found for k₁ = k₂ = 3 is (168, 322), where primeFactors of 169·170·171 = primeFactors of 323·324·325 = {2,3,5,13,17,19}.

The structural lemmas reduce the problem significantly: the second range must consist of smooth numbers, and in the boundary case the smoothness bound is a constant. However, the full proof requires:
- The S-unit equation theorem (not in Mathlib), which gives finiteness of consecutive smooth number runs
- An additional argument to simultaneously bound *both* n₁ and n₂ using both directions of the prime factor equality

Even with the S-unit equation theorem as an axiom, the reduction to the main theorem requires carefully combining the smoothness constraints from both directions, which is the core mathematical difficulty of this open problem.