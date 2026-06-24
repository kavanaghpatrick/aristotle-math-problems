import Mathlib

/-!
# Erdős Problem 267 — Fibonacci reciprocal sums irrational

**Conjecture (Erdős):** Let n₁ < n₂ < ⋯ be a sequence of positive integers with
n_{k+1}/n_k ≥ c > 1 for all k. Then ∑ 1/F(n_k) is irrational.

**Status:** OPEN.

### Known partial results
- ∑ 1/F(2^n) is irrational (Good, 1974).
- The full Fibonacci reciprocal sum ∑_{n≥1} 1/F(n) is irrational (André-Jeannin, 1991).

### Note on the formalization
The growth condition `c ≤ n (k+1) / n k` uses natural number (truncating) division,
so it effectively requires `n(k+1) ≥ 2 * n(k)`, which is stronger than the intended
real-valued ratio condition `(n(k+1) : ℝ) / n(k) ≥ c`. Even this stronger version
remains open.
-/

open scoped Topology

noncomputable section

/-- **Erdős Problem 267.** If `n` is a strictly monotone sequence of natural numbers
with `n(k+1)/n(k) ≥ c > 1` for all `k`, then `∑ 1/F(n(k))` is irrational.

This is an **open conjecture**. -/
theorem erdos_267 :
    ∀ (n : ℕ → ℕ) (c : ℚ), c > 1 → StrictMono n →
    (∀ k, c ≤ n (k+1) / n k) →
    Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ)) := by
  sorry

end
