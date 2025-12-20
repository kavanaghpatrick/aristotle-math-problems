import Mathlib

open Nat Finset

theorem erdos_931 : ∀ (k₁ : ℕ) (k₂ : ℕ), k₂ ≥ 3 → k₂ ≤ k₁ →
    { (n₁, n₂) : ℕ × ℕ | n₁ + k₁ ≤ n₂ ∧
      (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors }.Finite := by
  sorry
