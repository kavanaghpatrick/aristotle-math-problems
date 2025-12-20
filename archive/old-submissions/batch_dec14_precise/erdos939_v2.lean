/-
Erdos Problem #939 - Sums of r-powerful numbers
OPEN: For all r ≥ 4, can sum of r-2 coprime r-powerful numbers be r-powerful?

FIX: Define everything at TOP LEVEL (outside namespace) to avoid scoping issues
-/

import Mathlib

set_option maxHeartbeats 400000

/-- A natural number n is k-full (k-powerful) if for every prime factor p,
    we have p^k ∣ n. -/
def IsFull (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

/-- A Finset is coprime if gcd of all elements is 1. -/
def FinsetCoprime (S : Finset ℕ) : Prop := S.gcd id = 1

/-- The set of valid configurations for Erdős 939:
    - |S| = r - 2
    - Elements are coprime (gcd = 1)
    - Each element is r-full
    - The sum is r-full -/
def Erdos939Sums (r : ℕ) : Set (Finset ℕ) :=
  {S | S.card = r - 2 ∧ FinsetCoprime S ∧ IsFull r (∑ s ∈ S, s) ∧ ∀ s ∈ S, IsFull r s}

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
    {(a,b,c) | FinsetCoprime {a, b, c} ∧
      IsFull 3 a ∧ IsFull 3 b ∧ IsFull 3 c ∧
      a + b = c}.Infinite ↔ sorry := by
  sorry
