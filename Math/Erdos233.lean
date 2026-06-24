import Mathlib

open scoped BigOperators
open Asymptotics Filter Real Finset Nat

/-!
# Erdős Problem 233 — Sum of Squares of Prime Gaps

**Conjecture (Heath-Brown):** `∑_{n < N} (p_{n+1} - p_n)² = O(N (log N)²)`.

This is an open problem in analytic number theory; we record it as a formal statement.
-/

/-- The `n`-th prime gap: `p_{n+1} - p_n`, where `p_n` is the `n`-th prime (0-indexed). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- **Erdős Problem 233 (Open).**
The sum of squares of prime gaps satisfies
`∑_{n < N} (p_{n+1} - p_n)² = O(N (log N)²)`. -/
theorem erdos_233 :
    (fun N => ((∑ n ∈ Finset.range N, (primeGap n) ^ 2) : ℝ)) =O[atTop]
      fun N => (N : ℝ) * (Real.log N) ^ 2 := by
  classical
  sorry

