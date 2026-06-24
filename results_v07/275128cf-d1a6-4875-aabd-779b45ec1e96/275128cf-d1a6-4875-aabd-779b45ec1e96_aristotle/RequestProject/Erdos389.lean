import Mathlib

/-!
# Erdős Problem 389: Consecutive Products Divisibility

**Conjecture (Erdős):** For every positive integer `n`, there exists `k > 0` such that
the product `(n+1)(n+2)⋯(n+k)` divides `(n+k+1)(n+k+2)⋯(n+2k)`.

**Status:** OPEN. This is an unsolved conjecture.

## Notes

The divisibility condition is equivalent to asking that
`C(n+2k, k) / C(n+k, k)` is a positive integer, where `C` denotes the binomial
coefficient.

Computationally verified for small `n`:
- `n = 1`: `k = 5` works (ratio = 77)
- `n = 2`: `k = 4` works (ratio = 14)
- `n = 3`: `k = 207` works
- `n = 4`: `k = 206` works
- `n = 6`: `k = 984` works

The required values of `k` grow rapidly with `n`, and no closed-form expression
for `k` as a function of `n` is known.
-/

/-- Erdős Problem 389 (OPEN): For every positive integer n, there exists k > 0 such that
the product (n+1)(n+2)...(n+k) divides (n+k+1)(n+k+2)...(n+2k). -/
theorem erdos_389 : ∀ n : ℕ, n ≥ 1 →
    ∃ k : ℕ, k > 0 ∧
    (∏ i ∈ Finset.range k, (n + 1 + i)) ∣
    (∏ i ∈ Finset.range k, (n + k + 1 + i)) := by sorry
