/-
Erdős Problem #647 - τ(n) + n bound
OPEN: Is there n > 24 such that max_{m<n}(m + τ(m)) ≤ n + 2?

Key insight: This is decidable for specific n. The solved variant proves n=24 works.
The question is whether ANY n > 24 exists.

Strategy: Aristotle might find a specific counterexample or prove impossibility.
-/

import Mathlib

set_option maxHeartbeats 400000

open ArithmeticFunction

namespace Erdos647

/-- Is there some n > 24 such that max_{m<n}(m + τ(m)) ≤ n + 2? -/
theorem erdos_647 : (∃ n > 24, ⨆ m : Fin n, m + σ 0 m ≤ n + 2) ↔ sorry := by
  sorry

/-- This property holds for n = 24 (solved). -/
theorem twenty_four : ⨆ m : Fin 24, (m : ℕ) + σ 0 m ≤ 26 := by
  exact ciSup_le <| by decide

end Erdos647
