import Mathlib

set_option maxHeartbeats 800000

/-!
# Erdős Problem 366: 2-full followed by 3-full

**Problem:** Does there exist a positive integer `n` such that `n` is 2-full
(every prime divisor appears to power ≥ 2) and `n + 1` is 3-full (every prime
divisor appears to power ≥ 3)?

**Status:** OPEN. This is conjectured to be false (Erdős–Graham). Computational
search rules out any such `n < 10^22`. The ABC conjecture implies the set of
such `n` is finite. See: Bajpai–Bennett–Chan (2023), arXiv:2302.03113.

The *reverse* direction (n is 3-full and n+1 is 2-full) is satisfied by
(n, n+1) = (8, 9): 8 = 2³ is 3-full and 9 = 3² is 2-full.

## Results formalized

1. `consecutive_coprime`: Consecutive naturals are coprime.
2. `erdos_366_reverse`: The reverse direction, witnessed by (8, 9).
3. `no_erdos_366_pair_below`: Bounded non-existence via `native_decide`.
4. `erdos_366`: The open conjecture itself, left as `sorry`.
-/

/-! ## Definitions -/

/-- A natural number `n` is k-full if every prime divisor of `n` divides `n`
    to at least the k-th power. -/
def IsKFull (k : ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ k ∣ n

/-! ## Consecutive coprimality -/

/-- Consecutive natural numbers are coprime. -/
theorem consecutive_coprime (n : ℕ) : Nat.Coprime n (n + 1) := by
  simp [Nat.Coprime]

/-! ## Reverse direction: (8, 9) -/

/-- 8 is 3-full: the only prime divisor is 2, and 2³ = 8 divides 8. -/
theorem eight_is_three_full : IsKFull 3 8 := by
  intro p hp hd
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  have : p = 2 := by
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (h8 ▸ hd)
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 2) p h2) with h | h
    · exact absurd h (Nat.Prime.one_lt hp).ne'
    · exact h
  subst this; norm_num

/-- 9 is 2-full: the only prime divisor is 3, and 3² = 9 divides 9. -/
theorem nine_is_two_full : IsKFull 2 9 := by
  intro p hp hd
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  have : p = 3 := by
    have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (h9 ▸ hd)
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) p h3) with h | h
    · exact absurd h (Nat.Prime.one_lt hp).ne'
    · exact h
  subst this; norm_num

/-- The reverse direction of Erdős 366: there exists a positive `n` such that
    `n` is 3-full and `n + 1` is 2-full. Witnessed by `n = 8`. -/
theorem erdos_366_reverse :
    ∃ n : ℕ, 0 < n ∧ IsKFull 3 n ∧ IsKFull 2 (n + 1) :=
  ⟨8, by omega, eight_is_three_full, nine_is_two_full⟩

/-! ## Bounded non-existence -/

/-- Computable check for k-fullness using prime factorization. -/
def isKFullBool (k n : ℕ) : Bool :=
  n.primeFactorsList.all (fun p => p ^ k ∣ n)

/-- The Boolean check agrees with the mathematical definition for positive `n`. -/
theorem isKFullBool_iff {k n : ℕ} (hn : 0 < n) :
    isKFullBool k n = true ↔ IsKFull k n := by
  simp only [isKFullBool, List.all_eq_true, IsKFull]
  constructor
  · intro h p hp hpn
    have hmem : p ∈ n.primeFactorsList :=
      Nat.mem_primeFactorsList (by omega) |>.mpr ⟨hp, hpn⟩
    have := h p hmem
    rwa [decide_eq_true_eq] at this
  · intro h p hp
    rw [decide_eq_true_eq]
    obtain ⟨hpp, hpn⟩ := (Nat.mem_primeFactorsList (by omega)).mp hp
    exact h p hpp hpn

/-- No `n` in `{1, …, 10000}` satisfies: `n` is 2-full and `n + 1` is 3-full. -/
theorem no_erdos_366_pair_below :
    ∀ n ∈ Finset.Icc 1 10000,
      ¬(isKFullBool 2 n = true ∧ isKFullBool 3 (n + 1) = true) := by
  native_decide

/-! ## The open conjecture -/

/-- **Erdős Problem 366 (OPEN).**

This asks whether there exists a positive integer `n` such that `n` is 2-full
and `n + 1` is 3-full. This is an open problem; existence is conjectured
to be false (Erdős–Graham). No such `n` is known to exist, and computational
searches have verified non-existence up to `10^22`.

The ABC conjecture implies the set of such `n` is finite
(Bajpai–Bennett–Chan 2023, arXiv:2302.03113).

We leave this as `sorry` — it represents an open problem in number theory. -/
theorem erdos_366 :
    ∃ n : ℕ, 0 < n ∧
      (∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n) ∧
      (∀ p : ℕ, p.Prime → p ∣ (n + 1) → p ^ 3 ∣ (n + 1)) := by
  sorry
