# Summary of changes for run 38da55e5-43c9-4ddf-9536-cf52dc64c09d
## Erdős Problem 1052: Finitely Many Unitary Perfect Numbers

### Summary

This is an **open problem** since the 1960s. I formalized substantial infrastructure and proved all tractable results, leaving only the main open conjecture with `sorry`.

### What was accomplished (in `RequestProject/Main.lean`):

**Definitions:**
- `Nat.unitaryDivisors`: the set of unitary divisors of n (divisors d with gcd(d, n/d) = 1)
- `unitarySigma`: the unitary divisor sum σ*(n) = Σ_{d unitary divisor of n} d
- `IsUnitaryPerfect`: n is unitary perfect iff n ≥ 1 and σ*(n) = 2n

**Verified examples:**
- Computationally verified that 6, 60, 90, and 87360 are unitary perfect numbers

**Proved theorems (all sorry-free, standard axioms only):**
1. **`unitarySigma_prime_pow`**: σ*(p^a) = 1 + p^a for prime p
2. **`unitarySigma_mul_coprime`**: σ* is multiplicative — σ*(mn) = σ*(m)·σ*(n) when gcd(m,n) = 1
3. **`unitarySigma_eq_prod_one_add_pow`**: The product formula σ*(n) = ∏_{p ∈ primeFactors(n)} (1 + p^{v_p(n)})
4. **`IsUnitaryPerfect.even`**: Every unitary perfect number is even (using the 2-adic valuation argument: if n is odd with k prime factors, then 2^k | σ*(n) = 2n, forcing k ≤ 1, which leads to contradictions)
5. **`not_isUnitaryPerfect_prime_pow`**: No prime power is unitary perfect
6. **`wall_k2`**: The only unitary perfect number with exactly 2 prime factors is 6 (via the identity (p^a−1)(q^b−1) = 2)
7. **`unitarySigma_ge_one_plus_self`**: σ*(n) ≥ n+1 for n ≥ 2
8. **`IsUnitaryPerfect.two_le`**: Every unitary perfect number is ≥ 2

**Main conjecture (`erdos_1052`):**
- The conjectured answer is `True` (the set of unitary perfect numbers IS finite)
- The forward direction (True → Finite) remains `sorry` — this is the actual open problem
- The reverse direction is proved trivially

### Why the main conjecture cannot be fully proved:
The proposed proof strategy requires:
1. The **Bilu-Hanrot-Voutier primitive divisor theorem** (2001) — a deep number theory result not in Mathlib
2. **Wall's 1972 theorem** — finiteness of unitary perfect numbers with a fixed number of prime factors (for arbitrary k)
3. A **support-closure argument** bounding the number of prime factors uniformly

These are substantial mathematical results that would each require extensive formalization effort, and even then the full argument connecting them remains an open research problem.