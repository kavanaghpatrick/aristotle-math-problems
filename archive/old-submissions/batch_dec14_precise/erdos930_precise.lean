/-
Erdos Problem #930 - Products of Consecutive Integers
OPEN: For every r, exists k such that product of r disjoint intervals is never a power?

SIMPLE definitions - uses only Mathlib:
- Finset.Icc, product
- Nat.factorization
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

namespace Erdos930

/-- n is a perfect power if n = m^l for some l > 1.
    EXACT definition from FormalConjectures. -/
def IsPower (n : ℕ) : Prop :=
  ∃ m l, 1 < l ∧ m^l = n

/-- Returns the least prime >= k.
    EXACT definition from FormalConjectures. -/
def nextPrime (k : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes k)

/-- OPEN: For every r, there exists k such that the product of
    r disjoint intervals of consecutive integers (each of length >= k)
    is never a perfect power. -/
theorem erdos_930 :
    (∀ r > 0, ∃ k, ∀ I₁ I₂ : Fin r → ℕ,
      (∀ i : Fin r, 0 < I₁ i ∧ I₁ i + k ≤ I₂ i + 1) →
        (∀ i j : Fin r, i < j → I₂ i < I₁ j) →
          ¬ IsPower (∏ i : Fin r, ∏ m ∈ Icc (I₁ i) (I₂ i), m)) ↔ sorry := by
  sorry

/-- SOLVED: Product of consecutive integers is never a power (Erdős-Selfridge 1975).
    This is the r=1 case. -/
theorem erdos_930_consecutive :
    ∀ n k, 0 ≤ n → 2 ≤ k →
      ¬ IsPower (∏ m ∈ Icc (n + 1) (n + k), m) := by
  sorry

/-- Test: 2 * 3 * 4 = 24 is not a perfect power. -/
theorem test_234 : ¬ IsPower 24 := by
  intro ⟨m, l, hl, hml⟩
  interval_cases l
  all_goals { interval_cases m <;> simp_all }

end Erdos930
