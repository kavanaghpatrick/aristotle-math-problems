/-
Erdős Problem #939 - Sums of r-powerful numbers
OPEN: For all r ≥ 4, can sum of r-2 coprime r-powerful numbers be r-powerful?

Known: Examples exist for r = 5, 7, 8 (Cambie).
Open: Does this hold for ALL r ≥ 4?

This combines coprimality, powerful numbers, and sums.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos939

/-- A set S is in Erdos939Sums(r) if:
    - |S| = r - 2
    - S is coprime (gcd of all elements is 1)
    - Each element is r-powerful
    - The sum is r-powerful
-/
def Erdos939Sums (r : ℕ) : Set (Finset ℕ) :=
  {S | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧ ∀ s ∈ S, r.Full s}

/-- OPEN: Does Erdos939Sums(r) have elements for ALL r ≥ 4? -/
theorem erdos_939 : (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔ sorry := by
  sorry

/-- Known: There exist examples for r = 5 (Cambie).
    3761^5 = 2^8·3^10·5^7 + 2^12·23^6 + 11^5·13^5 -/
theorem examples_exist : ∃ r ≥ 4, (Erdos939Sums r).Nonempty := by
  use 5
  simp only [ge_iff_le, Nat.reduceLeDiff, true_and]
  unfold Erdos939Sums
  simp [Set.Nonempty]
  use {2^8 * 3^10 * 5^7, 2^12 * 23^6, 11^5 * 13^5}
  sorry

end Erdos939
