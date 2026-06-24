import Mathlib

set_option maxHeartbeats 16000000

/-! # Brocard's conjecture for n ≤ 500

We prove that for all n with 2 ≤ n ≤ 500, there are at least 4 primes strictly between
the squares of the n-th and (n+1)-th primes.

## Strategy

Instead of manually enumerating 500 prime values, we:
1. Define a **computable** nth-prime function `nthPrimeComp` using `Nat.find`.
2. Verify computationally (via `native_decide`) that:
   - `nthPrimeComp n` is prime for all n ≤ 501
   - `Nat.count Nat.Prime (nthPrimeComp n) = n` for all n ≤ 501
   - The Brocard condition holds for all n ∈ [2, 500]
3. Bridge `nthPrimeComp` to the noncomputable `Nat.nth Nat.Prime` using `Nat.nth_count`.

This approach scales to any bound without manual enumeration.
-/

/-- The smallest prime ≥ m. -/
def nextPrimeFrom (m : ℕ) : ℕ :=
  have : ∃ k, Nat.Prime (m + k) := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes m
    exact ⟨p - m, by rwa [Nat.add_sub_cancel' hp1]⟩
  m + Nat.find this

/-- Computable n-th prime (0-indexed): nthPrimeComp 0 = 2, nthPrimeComp 1 = 3, etc. -/
def nthPrimeComp : ℕ → ℕ
  | 0 => 2
  | n + 1 => nextPrimeFrom (nthPrimeComp n + 1)

/-- nthPrimeComp n is prime for all n ≤ 501. -/
private lemma nthPrimeComp_prime :
    ∀ n ∈ Finset.Icc 0 501, Nat.Prime (nthPrimeComp n) := by native_decide

/-- The count of primes below nthPrimeComp n equals n, for n ≤ 501. -/
private lemma nthPrimeComp_count :
    ∀ n ∈ Finset.Icc 0 501, Nat.count Nat.Prime (nthPrimeComp n) = n := by native_decide

/-- nthPrimeComp agrees with Nat.nth Nat.Prime for indices ≤ 501. -/
private lemma nthPrimeComp_eq_nth (n : ℕ) (hn : n ≤ 501) :
    Nat.nth Nat.Prime n = nthPrimeComp n := by
  have hp : Nat.Prime (nthPrimeComp n) :=
    nthPrimeComp_prime n (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hn⟩)
  have hc : Nat.count Nat.Prime (nthPrimeComp n) = n :=
    nthPrimeComp_count n (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hn⟩)
  conv_lhs => rw [← hc]
  exact Nat.nth_count hp

/-- The Brocard condition verified computationally using nthPrimeComp. -/
private lemma brocard_computable :
    ∀ n ∈ Finset.Icc 2 500,
      4 ≤ ((Finset.Ioo (nthPrimeComp n ^ 2) (nthPrimeComp (n + 1) ^ 2)).filter Nat.Prime).card := by
  native_decide

/-- **Brocard's conjecture** verified for n ≤ 500: for every n with 2 ≤ n ≤ 500,
there are at least 4 primes strictly between p_n² and p_{n+1}². -/
theorem brocard_conjecture_extended :
    ∀ n : ℕ, 2 ≤ n → n ≤ 500 →
      4 ≤ ((Finset.Ioo (n.nth Nat.Prime ^ 2) ((n + 1).nth Nat.Prime ^ 2)).filter
        Nat.Prime).card := by
  intro n hn1 hn2
  rw [nthPrimeComp_eq_nth n (by omega), nthPrimeComp_eq_nth (n + 1) (by omega)]
  exact brocard_computable n (Finset.mem_Icc.mpr ⟨hn1, hn2⟩)
