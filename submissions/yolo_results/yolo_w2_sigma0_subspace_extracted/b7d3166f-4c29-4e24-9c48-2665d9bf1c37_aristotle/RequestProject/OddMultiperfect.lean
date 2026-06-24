import Mathlib

/-!
# Odd multiperfect impossibility for σ₀(n) ∈ {11, 13, 17, 19}

For every odd natural number n > 1 whose divisor count σ₀(n) belongs to
{11, 13, 17, 19}, n is not multiperfect.

## Proof outline

1. Each q ∈ {11, 13, 17, 19} is prime.
2. If σ₀(n) = q (prime) and n > 1, then n = p^(q-1) for some prime p.
   (Because σ₀(n) = ∏(eᵢ+1) and a product of positive integers equaling
   a prime forces exactly one factor to be q and the rest to be 1.)
3. Since n is odd, p must be odd, hence p ≥ 3.
4. σ(p^(q-1)) = 1 + p + p² + ⋯ + p^(q-1) < 2·p^(q-1) = 2n for p ≥ 3.
5. But σ(n) = k·n with k ≥ 2 gives σ(n) ≥ 2n, contradiction.
-/

open Finset Nat in
/-- If `n > 0` and `(Nat.divisors n).card` is prime, then `n` is a prime power. -/
lemma isPrimePow_of_card_divisors_prime {n : ℕ} (hn : n ≠ 0)
    (hcard : Nat.Prime (Nat.divisors n).card) : IsPrimePow n := by
  convert isPrimePow_iff_card_primeFactors_eq_one.mpr _
  have h_prime_factors : ∀ {S : Finset ℕ} {f : ℕ → ℕ},
      (∀ x ∈ S, 1 < f x) → Nat.Prime (∏ x ∈ S, f x) → S.card = 1 := by
    intros S f hf hprod
    induction S using Finset.induction <;> simp_all +decide [Nat.prime_mul_iff]
    grind
  rw [Nat.card_divisors hn] at hcard
  exact h_prime_factors
    (fun x hx => Nat.succ_lt_succ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx))) hcard

/-- For `p ≥ 2` and `e ≥ 1`, the geometric sum `1 + p + ⋯ + p^e` is
strictly less than `2 * p^e`. -/
lemma geom_sum_lt_two_mul_top {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) :
    ∑ i ∈ Finset.range (e + 1), p ^ i < 2 * p ^ e := by
  induction he <;> simp_all +decide [Finset.sum_range_succ, pow_succ']
  · nlinarith [pow_pos (zero_lt_two.trans_le hp) ‹_›]
  · nlinarith [pow_pos (zero_lt_two.trans_le hp) ‹_›]

/-- The sum of divisors of a prime power equals the geometric sum. -/
lemma sigma_prime_pow_eq_geom_sum {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    (Nat.divisors (p ^ e)).sum id = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  rw [Nat.divisors_prime_pow hp]
  simp [Finset.sum_map]

/-- If n is a prime power p^e, then (Nat.divisors n).card = e + 1. -/
lemma card_divisors_prime_pow {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    (Nat.divisors (p ^ e)).card = e + 1 := by
  rw [Nat.divisors_prime_pow hp]
  simp

/-
For any prime q, no odd n > 1 with σ₀(n) = q is multiperfect.
-/
lemma no_odd_multiperfect_prime_sigma0 {q : ℕ} (hq : Nat.Prime q) :
    ¬ ∃ n : ℕ, Odd n ∧ n > 1 ∧
      (Nat.divisors n).card = q ∧
      ∃ k : ℕ, k ≥ 2 ∧ ((Nat.divisors n).sum id) = k * n := by
  intro ⟨ n, hn_odd, hn_gt_one, hn_card, k, hk_ge_two, h_divisors_sum ⟩
  -- Since σ₀(n) = q is prime, n is a prime power p^e with p prime and e ≥ 1.
  obtain ⟨p, e, hp, he, rfl⟩ : ∃ p e : ℕ, Nat.Prime p ∧ 1 ≤ e ∧ n = p ^ e := by
    have h_prime_power : IsPrimePow n := by
      exact isPrimePow_of_card_divisors_prime hn_gt_one.ne_bot ( hn_card ▸ hq );
    rw [ isPrimePow_nat_iff ] at h_prime_power ; aesop
  -- σ(p^e) = ∑ i in range (e+1), p^i < 2 * p^e by geom_sum_lt_two_mul_top.
  have h_sigma_lt_two_n : (Nat.divisors (p ^ e)).sum id < 2 * p ^ e := by
    convert geom_sum_lt_two_mul_top ( show 2 ≤ p by exact hp.two_le ) he using 1;
    convert sigma_prime_pow_eq_geom_sum hp e using 1;
  nlinarith

/-- Main theorem: for q ∈ {11, 13, 17, 19}, no odd n > 1 with σ₀(n) = q
is multiperfect. -/
theorem odd_multiperfect_sigma0_family_impossible :
    ∀ q ∈ ({11, 13, 17, 19} : Finset ℕ),
      ¬ ∃ n : ℕ, Odd n ∧ n > 1 ∧
        (Nat.divisors n).card = q ∧
        ∃ k : ℕ, k ≥ 2 ∧ ((Nat.divisors n).sum id) = k * n := by
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> exact no_odd_multiperfect_prime_sigma0 (by norm_num)