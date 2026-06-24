import Mathlib

theorem i9_smoke_infinitude_primes (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p := by
  exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( n + 1 ) )