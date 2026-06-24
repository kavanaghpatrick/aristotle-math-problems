import Mathlib

/-!
# Erdős-Straus Conjecture for n ≡ 1 (mod 840)

The Erdős-Straus conjecture states that 4/n = 1/x + 1/y + 1/z has a solution in
positive integers for all n ≥ 2. After known modular reductions (even n, n ≡ 3 mod 4,
n ≡ 2 mod 3, n ≡ 5 mod 8, n ≡ 5 mod 12, n ≡ 17 mod 20), the conjecture reduces to
n ≡ 1 mod 24, and further to n ≡ r mod 840 for r ∈ {1, 121, 169, 289, 361, 529}.

This file targets the case n ≡ 1 (mod 840), which is one of the remaining open cases.

## Counterexample to the original statement

The original statement quantified over all `k : ℕ`, but k = 0 gives n = 1, for which
no solution exists: the maximum value of 1/x + 1/y + 1/z for positive integers is 3
(attained at x = y = z = 1), which is strictly less than 4/1 = 4. The corrected
statement requires `k ≥ 1`, ensuring n = 840k + 1 ≥ 841 ≥ 2.

## Reduction to Egyptian fraction decomposition

For n = 840k + 1 with k ≥ 1, setting x = ⌈n/4⌉ = 210k + 1 gives:

  4/(840k+1) − 1/(210k+1) = 3/((840k+1)(210k+1))

So the problem reduces to decomposing 3/M as a sum of two unit fractions 1/y + 1/z,
where M = (840k+1)(210k+1). This is equivalent to finding a factorization
(3y−M)(3z−M) = M² with both factors ≡ 2 (mod 3).

Since M ≡ 1 (mod 3), such a factorization requires M² to have a divisor d ≡ 2 (mod 3),
which holds if and only if M has at least one prime factor p ≡ 2 (mod 3). When all
prime factors of M are ≡ 1 (mod 3), an alternative initial splitting (different x value)
must be used, and no single parametric family is known to cover all cases.

## Computational verification

The conjecture has been verified computationally for all n < 10^17. For the first 40
values of k ≥ 1, solutions were found using initial splittings with r = 4x − n ∈
{3, 7, 11, 15, 19, 23, 39}, but no uniform pattern emerges.

## Status

**OPEN.** This remains an unsolved case of the Erdős-Straus conjecture.
-/

-- The original statement is false for k = 0 (n = 1):
-- 1/x + 1/y + 1/z ≤ 3 < 4 = 4/1 for all positive integers x, y, z.
-- theorem erdos_straus_r1_original (k : ℕ) :
--     ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
--     4 * x * y * z = (840*k+1) * (y*z + x*z + x*y) := by
--   sorry

/-- **Erdős-Straus conjecture for n ≡ 1 (mod 840).**

The equation `4/n = 1/x + 1/y + 1/z` has a solution in positive integers for all
`n = 840k + 1` with `k ≥ 1`. This is equivalent (after clearing denominators) to the
Diophantine equation `4·x·y·z = n·(y·z + x·z + x·y)`.

This is an **open problem**, verified computationally for n < 10^17.

**Correction:** The original statement omitted the hypothesis `k ≥ 1`. For k = 0 (n = 1),
no solution exists since `1/x + 1/y + 1/z ≤ 3 < 4` for positive integers. -/
theorem erdos_straus_r1 (k : ℕ) (hk : k ≥ 1) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = (840*k+1) * (y*z + x*z + x*y) := by
  sorry
