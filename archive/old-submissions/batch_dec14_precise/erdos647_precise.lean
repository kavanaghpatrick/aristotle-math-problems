/-
Erdős Problem #647 - τ(n) + n bound
OPEN: Is there n > 24 such that max_{m<n}(m + τ(m)) ≤ n + 2?

Uses ONLY Mathlib definitions:
- σ 0 = divisor count function τ(n)
- Fin n for m < n
- iSup for maximum
-/

import Mathlib

set_option maxHeartbeats 400000

open ArithmeticFunction

namespace Erdos647

/-- OPEN: Is there some n > 24 such that max_{m<n}(m + τ(m)) ≤ n + 2?

    The EXACT formalization uses:
    - σ 0 m = number of divisors of m (this is τ(m))
    - Fin n iterates over m ∈ {0, 1, ..., n-1}
    - ⨆ computes the supremum (maximum for finite sets) -/
theorem erdos_647 : (∃ n > 24, ⨆ m : Fin n, (m : ℕ) + σ 0 m ≤ n + 2) ↔ sorry := by
  sorry

/-- SOLVED: This property holds for n = 24.
    Factorials less than 24 are checked. -/
theorem erdos_647_twenty_four : ⨆ m : Fin 24, (m : ℕ) + σ 0 m ≤ 26 := by
  exact ciSup_le <| by decide

/-- Erdős conjectured: lim_{n→∞} max_{m<n}(τ(m) + m - n) = ∞ -/
theorem erdos_647_lim :
    Filter.atTop.Tendsto (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) Filter.atTop ↔ sorry := by
  sorry

end Erdos647
