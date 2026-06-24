import Mathlib

/-!
# Erdős Problem 677 — LCM of consecutive intervals injective

For k > 0 and m ≥ n + k, is lcm(m+1,...,m+k) ≠ lcm(n+1,...,n+k)?

This is an **open problem** posed by Erdős. The condition m ≥ n + k ensures the
intervals {n+1,...,n+k} and {m+1,...,m+k} are disjoint (non-overlapping).

For the weaker "shifted" version (where intervals may overlap), the only known solutions are:
- lcm(4,5,6) = lcm(13,14) = 60
- lcm(3,4,5,6) = lcm(19,20) = 60

## Proof attempts and partial results

The most natural approach is to find a prime p in the interval [m+1, m+k].
If such a prime exists, then p > n+k (since m ≥ n+k), so p cannot divide
any element of [n+1, n+k], giving v_p(lcm(n+1,...,n+k)) = 0 while
v_p(lcm(m+1,...,m+k)) ≥ 1, a contradiction.

By Bertrand's postulate, there is a prime in (m, 2m], and since m ≥ k
(from m ≥ n + k ≥ k), we have m + k ≤ 2m. However, the Bertrand prime
may lie in (m+k, 2m] rather than in (m, m+k], so this approach does not
directly resolve the general case.

Stronger prime gap results (e.g., Ingham, Baker–Harman–Pintz) guarantee
primes in shorter intervals but only for sufficiently large m relative to k,
leaving finitely many cases unresolved.
-/

namespace Finset

/-- `lcmInterval n k` is the LCM of the k consecutive integers {n+1, n+2, ..., n+k}. -/
noncomputable def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Icc (n + 1) (n + k)).lcm id

end Finset

/-- **Erdős Problem 677** (Open Conjecture): For k > 0 and m ≥ n + k, the LCM of k
consecutive integers starting from m+1 is different from the LCM of k consecutive
integers starting from n+1. That is, lcm(m+1,...,m+k) ≠ lcm(n+1,...,n+k).

**Status: OPEN.** This remains an unsolved conjecture. -/
theorem erdos_677 :
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k →
    Finset.lcmInterval m k ≠ Finset.lcmInterval n k := by sorry
