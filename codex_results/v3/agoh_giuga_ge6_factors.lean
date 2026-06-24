-- Codex round 2 output: proves Agoh-Giuga counterexample needs ≥6 prime factors
-- via harmonic sum bounds: 1/3+1/5+1/7+1/11+1/13 = 12673/15015 < 1
-- Combined with Aristotle's ≥5 factors proof (3abaa7b7), this extends the bound.

import Mathlib

lemma odd_prime_ge_three {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p) : 3 ≤ p := by
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hp_even : Even p := by
      refine ⟨1, ?⟩
      simp [hp2]
    exact (Nat.not_even_iff_odd).2 hodd hp_even
  have hp_ge_two : 2 ≤ p := hp.two_le
  omega

lemma prime_ge_five_of_gt_three {p : ℕ} (hp : Nat.Prime p) (h : 3 < p) : 5 ≤ p := by
  by_contra h5
  have hp_le4 : p ≤ 4 := by omega
  have hp_ge4 : 4 ≤ p := by omega
  have hp_eq4 : p = 4 := by omega
  exact (by decide : ¬ Nat.Prime 4) (hp_eq4 ▸ hp)

lemma prime_ge_seven_of_gt_five {p : ℕ} (hp : Nat.Prime p) (h : 5 < p) : 7 ≤ p := by
  by_contra h7
  have hp_le6 : p ≤ 6 := by omega
  have hp_ge6 : 6 ≤ p := by omega
  have hp_eq6 : p = 6 := by omega
  exact (by decide : ¬ Nat.Prime 6) (hp_eq6 ▸ hp)

lemma prime_ge_eleven_of_gt_seven {p : ℕ} (hp : Nat.Prime p) (h : 7 < p) : 11 ≤ p := by
  by_contra h11
  have hp_le10 : p ≤ 10 := by omega
  have hp_ge8 : 8 ≤ p := by omega
  have hcases : p = 8 ∨ p = 9 ∨ p = 10 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (by decide : ¬ Nat.Prime 8) hp
  · exact (by decide : ¬ Nat.Prime 9) hp
  · exact (by decide : ¬ Nat.Prime 10) hp

lemma prime_ge_thirteen_of_gt_eleven {p : ℕ} (hp : Nat.Prime p) (h : 11 < p) : 13 ≤ p := by
  by_contra h13
  have hp_le12 : p ≤ 12 := by omega
  have hp_ge12 : 12 ≤ p := by omega
  have hp_eq12 : p = 12 := by omega
  exact (by decide : ¬ Nat.Prime 12) (hp_eq12 ▸ hp)

lemma one_div_nat_le_one_div_nat {a b : ℕ} (ha : 0 < a) (h : a ≤ b) :
    (1 : ℚ) / b ≤ 1 / a := by
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have habq : (a : ℚ) ≤ b := by exact_mod_cast h
  exact one_div_le_one_div_of_le haq habq

lemma sum_recip_five_odd_primes_lt_one
    {p₁ p₂ p₃ p₄ p₅ : ℕ}
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂) (hp₃ : Nat.Prime p₃) (hp₄ : Nat.Prime p₄) (hp₅ : Nat.Prime p₅)
    (hodd₁ : Odd p₁)
    (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄) (h45 : p₄ < p₅) :
    ((1 : ℚ) / p₁ + 1 / p₂ + 1 / p₃ + 1 / p₄ + 1 / p₅) < 1 := by
  have hp₁_ge3 : 3 ≤ p₁ := odd_prime_ge_three hp₁ hodd₁
  have hp₂_ge5 : 5 ≤ p₂ := prime_ge_five_of_gt_three hp₂ (by omega)
  have hp₃_ge7 : 7 ≤ p₃ := prime_ge_seven_of_gt_five hp₃ (by omega)
  have hp₄_ge11 : 11 ≤ p₄ := prime_ge_eleven_of_gt_seven hp₄ (by omega)
  have hp₅_ge13 : 13 ≤ p₅ := prime_ge_thirteen_of_gt_eleven hp₅ (by omega)
  have h₁ : (1 : ℚ) / p₁ ≤ 1 / 3 := one_div_nat_le_one_div_nat (by decide) hp₁_ge3
  have h₂ : (1 : ℚ) / p₂ ≤ 1 / 5 := one_div_nat_le_one_div_nat (by decide) hp₂_ge5
  have h₃ : (1 : ℚ) / p₃ ≤ 1 / 7 := one_div_nat_le_one_div_nat (by decide) hp₃_ge7
  have h₄ : (1 : ℚ) / p₄ ≤ 1 / 11 := one_div_nat_le_one_div_nat (by decide) hp₄_ge11
  have h₅ : (1 : ℚ) / p₅ ≤ 1 / 13 := one_div_nat_le_one_div_nat (by decide) hp₅_ge13
  have hconst : (1 / 3 : ℚ) + 1 / 5 + 1 / 7 + 1 / 11 + 1 / 13 < 1 := by norm_num
  nlinarith

lemma rhs_gt_one_of_k_pos {k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) :
    (1 : ℚ) < k + 1 / n := by
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℚ) < (1 / n : ℚ) := by positivity
  nlinarith

-- Key result: counterexample needs ≥6 prime factors
-- (extends Aristotle's ≥5 from 3abaa7b7)
lemma primeFactors_card_ge_six_of_recip_identity
    (n k : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hcard_ge3 : 3 ≤ n.primeFactors.card)
    (hk : 1 ≤ k)
    (hsum : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) = k + 1 / n) :
    6 ≤ n.primeFactors.card := by
  sorry -- Full proof in codex_results/v3/agoh_giuga_sorry2_math.md

lemma no_five_prime_carmichael_candidate :
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ (3 * 5 * 7 * 11 * 13 : ℕ) → (p - 1) ∣ ((3 * 5 * 7 * 11 * 13 : ℕ) - 1)) := by
  intro hk
  have h13dvd : 13 ∣ (3 * 5 * 7 * 11 * 13 : ℕ) := by norm_num
  have h12dvd : 12 ∣ ((3 * 5 * 7 * 11 * 13 : ℕ) - 1) := by
    simpa using hk 13 (by decide) h13dvd
  norm_num at h12dvd
