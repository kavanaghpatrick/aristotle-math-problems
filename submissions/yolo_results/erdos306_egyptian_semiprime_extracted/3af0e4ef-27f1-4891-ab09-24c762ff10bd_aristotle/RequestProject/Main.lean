import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000

/-- **Erdős Problem 306** (Erdős–Graham, 1980).

Every positive rational `q` with squarefree denominator admits an Egyptian-fraction
representation
  `q = 1/n₁ + 1/n₂ + ⋯ + 1/nₖ`
where `n₁ < n₂ < ⋯ < nₖ` and each `nᵢ` is a product of exactly two distinct primes
(i.e., `ω(nᵢ) = Ω(nᵢ) = 2`).

**Status:** OPEN. Known small cases exist (e.g., `1/3 = 1/6 + 1/10 + 1/15`), but the
universal statement over all positive rationals with squarefree denominator has resisted
all approaches since 1980. The analogous three-prime version was solved by
Butler–Erdős–Graham (posthumous) for integers, but the two-prime case remains open and
is explicitly flagged as not resolvable by finite computation.

The formalization uses `n : Fin (k+1) → ℕ` with `n 0 = 1` as an anchor to force
`n 1 > 1`, and the sum ranges over `Finset.Icc 1 (Fin.last k)`. -/
theorem erdos_306 :
    ∀ (q : ℚ), 0 < q → Squarefree q.den →
      ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ),
        n 0 = 1 ∧ StrictMono n ∧
        (∀ i ∈ Finset.Icc 1 (Fin.last k),
          ArithmeticFunction.cardDistinctFactors (n i) = 2 ∧
          ArithmeticFunction.cardFactors (n i) = 2) ∧
        q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  sorry
