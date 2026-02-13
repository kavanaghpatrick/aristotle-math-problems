import Mathlib

set_option maxHeartbeats 800000

/-!
# OEIS A34693: Bounded verification — for every n with 1 < n < 500, ∃ k < n with nk+1 prime

The OEIS A34693 conjecture states that for every n > 1, there exists k < n such that
n*k + 1 is prime. This is an open conjecture in number theory.

We verify this computationally for all n from 2 to 499 using native_decide.

For each n, the check is finite: test k = 1, 2, ..., n-1 and verify primality of n*k+1.
The largest number checked is 499 * 499 + 1 = 249002.

Reference: https://oeis.org/A34693
-/

/-- For every n with 1 < n < 500, there exists k < n such that n*k + 1 is prime.
This verifies the OEIS A34693 conjecture for small values. -/
theorem oeis_a34693_bounded_500 :
    ∀ n : Fin 500, 1 < (↑n : ℕ) →
      ∃ k : Fin 500, (↑k : ℕ) < (↑n : ℕ) ∧ ((↑n : ℕ) * (↑k : ℕ) + 1).Prime := by
  native_decide
