import Mathlib

open ArithmeticFunction

set_option maxHeartbeats 800000

/-!
# Erdős Problem 647 — Sophie Germain Residue Subclass

We prove that for n ≥ 3000 with 6∣n, n-1 prime, (n-2)/2 prime, and
either ((n-2)/2 - 1)/2 composite or (2·(n-2)/2 - 1)/3 composite,
there exists m < n with m + σ₀(m) > n + 2.
-/

local notation "σ" => ArithmeticFunction.sigma

/-
============================================================================
Helper lemma: composite number has ≥ 3 divisors
============================================================================
-/
lemma Nat.card_divisors_composite {c : ℕ} (hc : ¬ Nat.Prime c) (hc1 : 1 < c) :
    3 ≤ c.divisors.card := by
      -- Since $c$ is composite, there exists � a� divisor $p$ such that $1 < p < c$ and $p \mid c$.
      obtain ⟨p, hp1, hp2, hp3⟩ : ∃ p, 1 < p ∧ p < c ∧ p ∣ c := by
        exact Exists.imp ( by tauto ) ( Nat.exists_dvd_of_not_prime2 hc1 ( by simpa only [ ← Nat.prime_iff ] using hc ) );
      exact Finset.two_lt_card_iff.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩

/-
============================================================================
Helper: σ₀(3c) ≥ 6 for composite c ≥ 999
Uses multiplicativity: write c = 3^a · m with gcd(3,m)=1.
If m ≥ 2: σ₀(3c) = (a+2)·σ₀(m) ≥ min(2·3, 3·2) = 6.
If m = 1: c = 3^a ≥ 999, a ≥ 7, σ₀ = a+2 ≥ 9.
============================================================================
-/
lemma sigma0_three_mul_composite_ge6 {c : ℕ} (hc : ¬ Nat.Prime c) (hc_ge : 999 ≤ c) :
    6 ≤ (sigma 0 : ℕ → ℕ) (3 * c) := by
      -- By multiplicativity: σ₀(3c) = (a+2)·σ₀(m) ≥ min(2·3, 3·2) = 6.
      obtain ⟨a, m, ha, hm, hm_coprime⟩ : ∃ a m : ℕ, c = 3^a * m ∧ Nat.gcd 3 m = 1 ∧ m > 0 := by
        exact ⟨ Nat.factorization c 3, c / 3 ^ Nat.factorization c 3, by rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ], Nat.prime_three.coprime_iff_not_dvd.mpr ( Nat.not_dvd_ordCompl ( by norm_num ) ( by linarith ) ), Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( Nat.ordProj_dvd _ _ ) ) ( pow_pos ( by norm_num ) _ ) ⟩;
      -- By multiplicativity: σ₀(3c) = (a+2)·σ₀(m).
      have h_sigma : (sigma 0) (3 * c) = (a + 2) * (sigma 0) m := by
        have h_sigma : (sigma 0) (3^(a+1) * m) = (sigma 0) (3^(a+1)) * (sigma 0) m := by
          exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ( Nat.Coprime.pow_left _ hm );
        simp_all +decide [ pow_succ', mul_assoc, ArithmeticFunction.sigma ];
        rw [ show 3 * 3 ^ a = 3 ^ ( a + 1 ) by ring, Nat.divisors_prime_pow ] <;> norm_num;
      by_cases ha0 : a = 0;
      · simp_all +decide [ sigma_zero_apply ];
        linarith [ show Finset.card ( Nat.divisors m ) ≥ 3 by exact Nat.card_divisors_composite hc ( by linarith ) ];
      · by_cases hm1 : m = 1;
        · simp_all +decide [ ArithmeticFunction.sigma ];
          exact le_of_not_gt fun h => by interval_cases a <;> contradiction;
        · -- Since $m \neq 1$, we have $\sigma_0(m) \geq 2$.
          have h_sigma_m : (sigma 0) m ≥ 2 := by
            grind +suggestions;
          nlinarith only [ h_sigma, h_sigma_m, Nat.pos_of_ne_zero ha0 ]

/-
============================================================================
Helper: σ₀(4d) ≥ 7 for composite d ≥ 749
Write d = 2^a · m with m odd.
If a = 0 (d odd): σ₀(4d) = 3·σ₀(d) ≥ 3·3 = 9.
If a ≥ 1, m ≥ 3: σ₀ = (a+3)·σ₀(m) ≥ 4·2 = 8.
If a ≥ 1, m = 1: d = 2^a ≥ 749, a ≥ 10, σ₀ = a+3 ≥ 13.
============================================================================
-/
lemma sigma0_four_mul_composite_ge7 {d : ℕ} (hd : ¬ Nat.Prime d) (hd_ge : 749 ≤ d) :
    7 ≤ (sigma 0 : ℕ → ℕ) (4 * d) := by
      -- Since $d$ is composite (not prime, $d \geq 749 > 1$), $d$ has a proper divisor.
      -- Write $d = 2^a * m$ where $m$ is odd ($\gcd(2,m) = 1$). Then $4 * d = 2^(a + 2) * m$.
      obtain ⟨a, m, hm_odd, hm_eq⟩ : ∃ a m, m % 2 = 1 ∧ d = 2^a * m := by
        -- By definition of exponentiation, we can write $d$ as $2^a \cdot m$ where $m$ is odd.
        use Nat.factorization d 2, d / 2^Nat.factorization d 2
        have hm_odd : (d / 2^Nat.factorization d 2) % 2 = 1 := by
          exact Nat.mod_two_ne_zero.mp fun contra => absurd ( Nat.dvd_of_mod_eq_zero contra ) ( Nat.not_dvd_ordCompl ( by norm_num ) <| by linarith )
        exact ⟨hm_odd, by
          rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ]⟩;
      -- By multiplicativity: $\sigma_0(4d) = \sigma_0(2^{a+2}) \cdot \sigma_0(m) = (a+3) \cdot \sigma_0(m)$.
      have h_sigma_mul : (sigma 0) (4 * d) = (a + 3) * (sigma 0) m := by
        -- By multiplicativity: $\sigma_0(4d) = \sigma_0(2^{a+2}) \cdot \sigma_0(m)$.
        have h_sigma_mul : (sigma 0) (4 * d) = (sigma 0) (2^(a+2)) * (sigma 0) m := by
          have h_sigma_mul : ArithmeticFunction.IsMultiplicative (sigma 0) := by
            convert ArithmeticFunction.isMultiplicative_sigma using 1;
          rw [ show 4 * d = 2 ^ ( a + 2 ) * m by rw [ hm_eq ] ; ring ] ; exact h_sigma_mul.2 ( show Nat.Coprime ( 2 ^ ( a + 2 ) ) m from Nat.Coprime.pow_left _ <| Nat.prime_two.coprime_iff_not_dvd.mpr <| by rw [ Nat.dvd_iff_mod_eq_zero ] ; aesop ) ;
        simp_all +decide [ sigma_zero_apply ];
        norm_num [ Nat.divisors_prime_pow ];
      rcases a with ( _ | _ | a ) <;> simp_all +arith +decide [ Nat.pow_succ', mul_assoc ];
      · by_contra h_contra;
        exact hd ( by have := Nat.card_divisors_composite hd ( by linarith ) ; norm_num [ sigma_zero_apply ] at * ; linarith );
      · grind +suggestions;
      · rcases m with ( _ | _ | m ) <;> simp_all +arith +decide;
        · exact le_of_not_gt fun h => by interval_cases a <;> contradiction;
        · rcases k : sigma 0 ( m + 2 ) with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.mul_succ ]

/-
============================================================================
Arithmetic helper: if 6∣n and (n-2)/2 is an odd prime (≥3), then 12∣n
============================================================================
-/
lemma div_six_even_of_prime {n : ℕ} (hn : n ≥ 3000) (h6 : 6 ∣ n)
    (hq : Nat.Prime ((n - 2) / 2)) : 2 ∣ (n / 6) := by
      cases Nat.Prime.eq_two_or_odd hq <;> omega

/-
============================================================================
Arithmetic: n - 3 = 3 * ((2 * ((n-2)/2) - 1) / 3) when 12 | n and n ≥ 12
============================================================================
-/
lemma n_sub_three_eq {n : ℕ} (hn : n ≥ 3000) (h12 : 12 ∣ n) :
    n - 3 = 3 * ((2 * ((n - 2) / 2) - 1) / 3) := by
      omega

/-
============================================================================
Arithmetic: n - 4 = 4 * ((((n-2)/2) - 1) / 2) when 12 | n and n ≥ 12
============================================================================
-/
lemma n_sub_four_eq {n : ℕ} (hn : n ≥ 3000) (h12 : 12 ∣ n) :
    n - 4 = 4 * ((((n - 2) / 2) - 1) / 2) := by
      omega

/-
============================================================================
Bound: ((2 * ((n-2)/2) - 1) / 3) ≥ 999 when n ≥ 3000 and 12 | n
============================================================================
-/
lemma c2_ge_999 {n : ℕ} (hn : n ≥ 3000) (h12 : 12 ∣ n) :
    999 ≤ (2 * ((n - 2) / 2) - 1) / 3 := by
      omega

/-
============================================================================
Bound: ((((n-2)/2) - 1) / 2) ≥ 749 when n ≥ 3000 and 12 | n
============================================================================
-/
lemma c1_ge_749 {n : ℕ} (hn : n ≥ 3000) (h12 : 12 ∣ n) :
    749 ≤ (((n - 2) / 2) - 1) / 2 := by
      omega

-- ============================================================================
-- Not prime → composite (> 1) for numbers ≥ 2
-- ============================================================================

lemma not_prime_gt_one {c : ℕ} (hc2 : c ≥ 2) : 1 < c := by omega

/-
============================================================================
Main Theorem
============================================================================
-/
theorem erdos_647_sophie_subclass
    (n : ℕ) (hn : n ≥ 3000) (h6 : 6 ∣ n)
    (hp1 : Nat.Prime (n-1)) (hq : Nat.Prime ((n-2)/2))
    (hsplit : ¬ Nat.Prime ((((n-2)/2) - 1) / 2)
              ∨ ¬ Nat.Prime ((2 * ((n-2)/2) - 1) / 3)) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + (σ 0 : ℕ → ℕ) m := by
      -- By div_six_even_of_prime, we have 2 ∣ (n/6), which combined with h6 gives 12 ∣ n.
      have h12 : 12 ∣ n := by
        cases Nat.Prime.eq_two_or_odd hq <;> omega;
      rcases hsplit with hsplit | hsplit <;> [ refine ⟨ ⟨ n - 4, Nat.sub_lt ( by linarith ) ( by linarith ) ⟩, ?_ ⟩ ; refine ⟨ ⟨ n - 3, Nat.sub_lt ( by linarith ) ( by linarith ) ⟩, ?_ ⟩ ] <;> norm_num [ Nat.add_sub_of_le ( show 4 ≤ n by linarith ), Nat.add_sub_of_le ( show 3 ≤ n by linarith ) ] at *;
      · -- By sigma0_four_mul_composite_ge7, we have σ₀(4 * c₁) ≥ 7.
        have h_sigma_four_mul_composite : 7 ≤ (sigma 0) (4 * (((n - 2) / 2 - 1) / 2)) := by
          apply sigma0_four_mul_composite_ge7 hsplit (c1_ge_749 hn h12);
        grind;
      · -- By sigma0_three_mul_composite_ge6, we have (σ 0) (3 * ((2 * ((n - 2) / 2) - 1) / 3)) ≥ 6.
        have h_sigma : (sigma 0) (3 * ((2 * ((n - 2) / 2) - 1) / 3)) ≥ 6 := by
          apply sigma0_three_mul_composite_ge6 hsplit (c2_ge_999 hn h12);
        grind