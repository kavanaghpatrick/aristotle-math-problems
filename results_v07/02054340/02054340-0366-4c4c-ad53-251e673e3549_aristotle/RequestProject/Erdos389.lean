import Mathlib

/-!
# Erdős Problem 389 — Consecutive Product Divisibility

**Conjecture (Erdős):** For every `n ≥ 1`, there exists `k ≥ 1` such that the product
`n(n+1)⋯(n+k-1)` divides the product `(n+k)(n+k+1)⋯(n+2k-1)`.

Equivalently, `C(n+2k-1, k) / C(n+k-1, k)` is a positive integer.

## Status

**OPEN.** This conjecture remains unproven as of 2025. The minimal `k = k(n)` satisfying the
divisibility grows extremely fast — roughly as `3^n`.

## Computational evidence

| n | min k |
|---|-------|
| 1 | 1     |
| 2 | 5     |
| 3 | 4     |
| 4 | 207   |
| 5 | 206   |
| 7 | 984   |

For `n = 1`, any `k ≥ 1` works since the first product is just `1`.

## Known partial results

- `k = n` does **not** always yield a valid `k` (fails for `n = 2`).
- The ratio can be expressed via p-adic valuations and Kummer's theorem (counting
  carries in base-p addition), but controlling carries for all primes simultaneously
  remains the core difficulty.
-/

/--
Erdős Problem 389: For every `n ≥ 1`, there exists `k ≥ 1` such that the product
`n(n+1)⋯(n+k-1)` divides the product `(n+k)(n+k+1)⋯(n+2k-1)`.

This is an **open problem** in combinatorial number theory.
-/
theorem erdos_389 : ∀ n : ℕ, n ≥ 1 →
    ∃ k : ℕ, k ≥ 1 ∧
    (∏ i ∈ Finset.range k, (n + i)) ∣
    (∏ i ∈ Finset.range k, (n + k + i)) := by sorry
