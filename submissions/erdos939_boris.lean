import Mathlib

open Nat Finset

def Nat.Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

@[reducible] def Finset.Coprime (S : Finset ℕ) : Prop := S.gcd id = 1

def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧ ∀ s ∈ S, r.Full s}

theorem erdos_939 : ∀ r ≥ 4, (Erdos939Sums r).Nonempty := by
  sorry
