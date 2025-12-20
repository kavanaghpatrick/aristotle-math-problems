import Mathlib

abbrev S730 :=
  {(n, m) : ℕ × ℕ | n < m ∧ n.centralBinom.primeFactors = m.centralBinom.primeFactors}

theorem erdos_730 : S730.Infinite := by
  sorry
