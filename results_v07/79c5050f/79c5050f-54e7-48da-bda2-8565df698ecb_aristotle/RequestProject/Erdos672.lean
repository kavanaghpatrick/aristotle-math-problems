import Mathlib

/-!
# Erdős Problem 672 (k = 35)

For `n, d > 0` with `gcd(n, d) = 1`, the product of `k` consecutive terms in arithmetic
progression `n(n+d)(n+2d)···(n+(k-1)d)` is never a perfect `l`-th power for any `l ≥ 2`.

## Background

- **Erdős–Selfridge (1975)**: Proved the case `d = 1` (product of consecutive integers).
- **Bennett–Bruin–Győry–Hajdu (2006)**: Proved cases `k ≤ 11`.
- **Győry–Hajdu–Pintér (2009)**: Extended to `k ≤ 34`.
- **Bennett–Siksek (2020)**: Proved the result for `k` sufficiently large.

## Status

**OPEN.** The case `k = 35` is the first unsolved case. The gap `35 ≤ k ≤ threshold`
(where threshold is the effective bound from Bennett–Siksek) remains open.

The known approaches use a combination of:
1. Showing each AP term `n + i·d` factors as a "smooth part" times an `l`-th power,
   exploiting the coprimality `gcd(n, d) = 1`.
2. Reducing to systems of Thue–Mahler equations or hyperelliptic/superelliptic curves.
3. For `l = 2`, using Galois representations and modularity.

For `k = 35`, the combinatorial explosion in the case analysis (particularly the
number of possible "smooth part" patterns and resulting Thue–Mahler equations) has
so far prevented a complete resolution.
-/

open Finset BigOperators

/-- **Erdős Problem 672 (k = 35)**: For `n, d > 0` with `gcd(n, d) = 1`,
the product `n(n+d)(n+2d)···(n+34d)` is never a perfect `l`-th power for `l ≥ 2`.

This is an **open problem**. -/
theorem erdos_672_k35 :
    ∀ n d : ℕ, n > 0 → d > 0 → n.gcd d = 1 →
    ∀ l : ℕ, l ≥ 2 →
    ¬ ∃ y : ℕ, (∏ i ∈ Finset.range 35, (n + i * d)) = y ^ l := by
  sorry
