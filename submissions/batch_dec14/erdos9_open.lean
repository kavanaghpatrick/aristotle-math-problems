/-
Erdős Problem #9 - Odd numbers not of form p + 2^k + 2^l
OPEN: Is the upper density of this set positive?

The set is known to be INFINITE (solved variant).
The open question is about density.

Strategy: This connects density theory to prime gaps and powers of 2.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos9

/-- Odd numbers not expressible as prime + 2^k + 2^l -/
def A : Set ℕ := { n | Odd n ∧ ¬ ∃ (p k l : ℕ), p.Prime ∧ n = p + 2 ^ k + 2 ^ l }

/-- 1 is in the set (trivially, since no prime + powers ≥ 3 equals 1) -/
theorem one_mem : 1 ∈ A := by
  constructor
  · decide
  · push_neg
    intro p k l hp
    linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]

/-- 3 is in the set -/
theorem three_mem : 3 ∈ A := by
  constructor
  · decide
  · push_neg
    intro p k l hp
    linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]

/-- The OPEN question: Is the upper density positive? -/
theorem erdos_9 : 0 < A.upperDensity ↔ sorry := by
  sorry

end Erdos9
