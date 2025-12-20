/-
Erdős Problem #939 - Sums of r-powerful numbers
OPEN: For all r ≥ 4, can sum of r-2 coprime r-powerful numbers be r-powerful?

PRECISE DEFINITIONS from FormalConjectures/ForMathlib:
- Nat.Full k n := ∀ p ∈ n.primeFactors, p^k ∣ n
- Finset.Coprime S := S.gcd id = 1
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos939

/-- A natural number n is k-full (k-powerful) if for every prime factor p,
    we have p^k ∣ n. This is the EXACT definition from FormalConjectures. -/
def Nat.Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

/-- A Finset is coprime if gcd of all elements is 1.
    This is the EXACT definition from FormalConjectures. -/
@[reducible] def Finset.Coprime (S : Finset ℕ) : Prop := S.gcd id = 1

/-- The set of valid configurations for Erdős 939:
    - |S| = r - 2
    - Elements are pairwise coprime (gcd = 1)
    - Each element is r-full
    - The sum is r-full -/
def Erdos939Sums (r : ℕ) : Set (Finset ℕ) :=
  {S | S.card = r - 2 ∧ S.Coprime ∧ Nat.Full r (∑ s ∈ S, s) ∧ ∀ s ∈ S, Nat.Full r s}

/-- OPEN: Does Erdos939Sums(r) have elements for ALL r ≥ 4?
    This asks: for every r ≥ 4, can we find r-2 coprime r-powerful numbers
    whose sum is also r-powerful? -/
theorem erdos_939 : (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔ sorry := by
  sorry

/-- Variant: Are there infinitely many such configurations for each r ≥ 4? -/
theorem erdos_939_infinite : (∀ r ≥ 4, (Erdos939Sums r).Infinite) ↔ sorry := by
  sorry

/-- Variant: Infinitely many triples of coprime 3-powerful numbers a,b,c with a+b=c?
    (This was proved by Nitaj 1995) -/
theorem erdos_939_triples :
    {(a,b,c) | ({a, b, c} : Finset ℕ).Coprime ∧
      Nat.Full 3 a ∧ Nat.Full 3 b ∧ Nat.Full 3 c ∧
      a + b = c}.Infinite ↔ sorry := by
  sorry

end Erdos939
