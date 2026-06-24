import Mathlib

open scoped BigOperators Nat

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 141 Variant — 11 Consecutive Primes in Arithmetic Progression

Do there exist 11 consecutive primes in arithmetic progression?
That is, do there exist primes p, p+d, p+2d, …, p+10d such that
these are consecutive primes (no prime lies strictly between any two
consecutive terms)?

## Status

This is an **open problem**. The case k ≤ 10 was settled in 1998 by
Lander and Parkin, who found an explicit 10-term consecutive prime AP
with common difference 210. The case k = 11 remains unresolved.
-/

/-- A set of natural numbers forms a consecutive prime arithmetic progression of length `k`
if there exist `p` and `d` such that:
1. The set is exactly `{p, p+d, p+2d, …, p+(k-1)d}`.
2. All elements are prime.
3. They are consecutive primes: no prime lies strictly between consecutive terms.
-/
def Set.IsAPAndPrimeProgressionOfLength (s : Set ℕ) (k : ℕ) : Prop :=
  ∃ (p d : ℕ), 0 < d ∧
    s = ↑(Finset.image (fun i => p + i * d) (Finset.range k)) ∧
    (∀ i, i < k → Nat.Prime (p + i * d)) ∧
    (∀ i, i + 1 < k → ∀ q, Nat.Prime q → p + i * d < q → q < p + (i + 1) * d → False)

/-- **Erdős 141 variant (k = 11)**: There exist 11 consecutive primes in arithmetic progression.

This is an open problem. -/
theorem erdos_141_eleven :
    ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength 11 := by
  sorry
