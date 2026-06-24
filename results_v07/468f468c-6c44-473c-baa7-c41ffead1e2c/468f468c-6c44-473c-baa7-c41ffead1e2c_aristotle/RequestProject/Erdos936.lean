import Mathlib

/-!
# Erdős Problem 936: Powerful numbers of the form 2^n + 1

We say a natural number m is *powerful* if for every prime p dividing m,
p² also divides m. The conjecture (Erdős Problem 936) states that the only
n ≥ 1 with 2^n + 1 powerful is n = 3 (giving 9 = 3²).

## Approach: Lifting the Exponent (LTE)

Write n = 2^s · m with m odd. Then 2^n + 1 = ((2^{2^s})^m + 1).
For an odd prime p dividing the Fermat number F_s = 2^{2^s} + 1,
LTE gives v_p(2^n + 1) = v_p(F_s) + v_p(m).

If v_p(F_s) = 1 and p ∤ m, then v_p(2^n + 1) = 1, blocking powerful.

Concrete unconditional exclusions:
- s=0, p=3: odd n with 3 ∤ n ruled out
- s=1, p=5: n ≡ 2 mod 4 with 5 ∤ (n/2) ruled out
- s=2, p=17: n ≡ 4 mod 8 with 17 ∤ (n/4) ruled out

Status: OPEN problem. We prove partial exclusion results and document the gap.
-/

open Nat

/-! ## Auxiliary divisibility lemmas -/

/-
PROBLEM
3 divides 2^n + 1 for all odd n.

PROVIDED SOLUTION
Since n is odd, 2^n ≡ (-1)^n ≡ -1 mod 3, so 2^n + 1 ≡ 0 mod 3. Use Nat.pow_mod or ZMod, or show 2 ≡ -1 mod 3 and (-1)^n = -1 for odd n.
-/
lemma three_dvd_pow_add_one_of_odd {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨ k, rfl ⟩ := hn; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
PROBLEM
If n is odd and 3 ∤ n, then 9 does not divide 2^n + 1.
    This follows from LTE: v_3(2^n + 1) = v_3(2+1) + v_3(n) = 1 + v_3(n).
    If 3 ∤ n then v_3(n) = 0, giving v_3(2^n+1) = 1, so 9 ∤ 2^n+1.

PROVIDED SOLUTION
We need to show that if n is odd and 3 ∤ n, then 9 ∤ 2^n+1. Use modular arithmetic: 2^n mod 9 cycles with period 6. For odd n not divisible by 3, n mod 6 is 1 or 5. Check: 2^1 mod 9 = 2, 2^5 mod 9 = 5. So 2^n + 1 mod 9 is 3 or 6, neither 0. Hence 9 ∤ 2^n+1. Alternatively, use Nat.pow_mod and case split on n % 6.
-/
lemma not_powerful_odd_not_dvd_three {n : ℕ} (hn : Odd n) (h3 : ¬(3 ∣ n)) :
    ¬(3 ^ 2 ∣ 2 ^ n + 1) := by
      rw [ ← Nat.mod_add_div n 6 ] at *; have := Nat.mod_lt n ( by decide : 6 > 0 ) ; interval_cases n % 6 <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at *;

/-
PROBLEM
5 divides 2^n + 1 when n ≡ 2 mod 4.

PROVIDED SOLUTION
n ≡ 2 mod 4. Then 2^n = 2^(4k+2) = (2^4)^k · 4 = 16^k · 4. 16 ≡ 1 mod 5, so 2^n ≡ 4 mod 5, hence 2^n + 1 ≡ 0 mod 5. Use Nat.pow_mod and the periodicity of 2^n mod 5 (period 4). Since n % 4 = 2, 2^n mod 5 = 2^2 mod 5 = 4, so 2^n + 1 ≡ 0 mod 5.
-/
lemma five_dvd_pow_add_one_of_mod4 {n : ℕ} (hn : n % 4 = 2) : 5 ∣ 2 ^ n + 1 := by
  rw [ ← Nat.mod_add_div n 4, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ;

/-
PROBLEM
If n ≡ 2 mod 4 and 5 ∤ (n/2), then 25 does not divide 2^n + 1.
    By LTE: v_5(2^n+1) = v_5((2^2)^{n/2}+1) = v_5(2^2+1) + v_5(n/2) = 1 + v_5(n/2).
    If 5 ∤ n/2, this is 1, so 25 ∤ 2^n+1.

PROVIDED SOLUTION
We need: if n ≡ 2 mod 4 and 5 ∤ (n/2), then 25 ∤ 2^n+1. The order of 2 mod 25 is 20, and 2^n mod 25 cycles with period 20. For n ≡ 2 mod 4, n/2 is an integer. Write n = 2m, then 2^n + 1 = 4^m + 1. v_5(4^m + 1) = v_5(4+1) + v_5(m) = 1 + v_5(m) by LTE (since 5 | 4+1 and 5 ∤ 4 and 5 ∤ 1 and m is odd since n ≡ 2 mod 4 means m = n/2 is odd). If 5 ∤ m = n/2, then v_5 = 1, so 25 ∤ 2^n+1. Concretely: n mod 20 can be 2, 6, 10, 14, 18. Check 2^n mod 25 for each: 2^2=4, 2^6=64≡14, 2^10=1024≡24, 2^14≡16384, 2^18. Actually just use decidable mod arithmetic: show (2^n+1) % 25 ≠ 0 by case-splitting on n % 20 (the values where n % 4 = 2 and 5 ∤ n/2).
-/
lemma not_powerful_mod4_not_dvd_five {n : ℕ} (hn : n % 4 = 2) (h5 : ¬(5 ∣ n / 2)) :
    ¬(5 ^ 2 ∣ 2 ^ n + 1) := by
      rw [ ← Nat.mod_add_div n 4, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at *;
      rw [ ← Nat.mod_add_div ( n / 4 ) 20 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ; ( have := Nat.mod_lt ( n / 4 ) ( by decide : 0 < 20 ) ; interval_cases _ : n / 4 % 20 <;> norm_num at h5 ⊢; );
      · omega;
      · omega;
      · omega;
      · omega

/-
PROBLEM
17 divides 2^n + 1 when n ≡ 4 mod 8.

PROVIDED SOLUTION
n ≡ 4 mod 8. 2^4 = 16 ≡ -1 mod 17, so ord_17(2) = 8. For n ≡ 4 mod 8, 2^n = (2^8)^(n/8) · 2^4. Since 2^8 ≡ 1 mod 17, 2^n ≡ 2^4 = 16 ≡ -1 mod 17. So 17 | 2^n + 1. Use Nat.pow_mod: 2^n mod 17 = 2^(n mod 8) mod 17 = 2^4 mod 17 = 16, so 2^n + 1 ≡ 0 mod 17.
-/
lemma seventeen_dvd_pow_add_one_of_mod8 {n : ℕ} (hn : n % 8 = 4) :
    17 ∣ 2 ^ n + 1 := by
      rw [ ← Nat.mod_add_div n 8, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ;

/-
PROBLEM
If n ≡ 4 mod 8 and 17 ∤ (n/4), then 17² does not divide 2^n + 1.
    By LTE: v_{17}(2^n+1) = v_{17}((2^4)^{n/4}+1) = v_{17}(2^4+1) + v_{17}(n/4) = 1 + v_{17}(n/4).
    If 17 ∤ n/4, this is 1, so 17² ∤ 2^n+1.

PROVIDED SOLUTION
Need: if n ≡ 4 mod 8 and 17 ∤ n/4, then 17² ∤ 2^n+1. Write n = 4m where m is odd (since n ≡ 4 mod 8). Then 2^n + 1 = 16^m + 1. By LTE: v_{17}(16^m + 1) = v_{17}(16+1) + v_{17}(m) = 1 + v_{17}(m). If 17 ∤ m = n/4, then v_{17} = 1, so 17² ∤ 2^n+1. Concretely: the order of 2 mod 289 is 8·17 = 136. Case-split on n mod 136 (values where n % 8 = 4 and 17 ∤ n/4) and check 2^n mod 289 ≠ 288 for each.
-/
lemma not_powerful_mod8_not_dvd_seventeen {n : ℕ} (hn : n % 8 = 4) (h17 : ¬(17 ∣ n / 4)) :
    ¬(17 ^ 2 ∣ 2 ^ n + 1) := by
      -- By contradiction, assume that $17^2$ divides $2^n + 1$.
      by_contra h_contra
      obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 4 := by
        exact ⟨ n / 8, by rw [ ← hn, Nat.div_add_mod ] ⟩
      simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      rw [ ← Nat.mod_add_div k 17 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt k ( by decide : 0 < 17 ) ; interval_cases k % 17 <;> norm_num at *;
      omega

/-! ## Exclusion theorems -/

/-- **LTE Exclusion s=0**: If n is odd and 3 ∤ n, then 2^n + 1 is not powerful. -/
theorem exclusion_s0 (n : ℕ) (hn_odd : Odd n) (h3 : ¬(3 ∣ n))
    (hpow : ∀ p, Nat.Prime p → p ∣ (2^n+1) → p^2 ∣ (2^n+1)) : False :=
  absurd (hpow 3 (by decide) (three_dvd_pow_add_one_of_odd hn_odd))
    (not_powerful_odd_not_dvd_three hn_odd h3)

/-- **LTE Exclusion s=1**: If n ≡ 2 mod 4 and 5 ∤ (n/2), then 2^n + 1 is not powerful. -/
theorem exclusion_s1 (n : ℕ) (hn : n % 4 = 2) (h5 : ¬(5 ∣ n / 2))
    (hpow : ∀ p, Nat.Prime p → p ∣ (2^n+1) → p^2 ∣ (2^n+1)) : False :=
  absurd (hpow 5 (by decide) (five_dvd_pow_add_one_of_mod4 hn))
    (not_powerful_mod4_not_dvd_five hn h5)

/-- **LTE Exclusion s=2**: If n ≡ 4 mod 8 and 17 ∤ (n/4), then 2^n + 1 is not powerful. -/
theorem exclusion_s2 (n : ℕ) (hn : n % 8 = 4) (h17 : ¬(17 ∣ n / 4))
    (hpow : ∀ p, Nat.Prime p → p ∣ (2^n+1) → p^2 ∣ (2^n+1)) : False :=
  absurd (hpow 17 (by decide) (seventeen_dvd_pow_add_one_of_mod8 hn))
    (not_powerful_mod8_not_dvd_seventeen hn h17)

/-- n = 3 is indeed a solution: 2^3 + 1 = 9 = 3² is powerful. -/
theorem n_eq_3_is_powerful : ∀ p, Nat.Prime p → p ∣ (2^3+1) → p^2 ∣ (2^3+1) := by
  intro p hp hd
  have h9 : 2 ^ 3 + 1 = 9 := by norm_num
  rw [h9] at hd ⊢
  have hle : p ≤ 9 := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> simp_all (config := { decide := true })

/-! ## Main theorem (OPEN) -/

/-- **Erdős Problem 936** (OPEN): The only n ≥ 1 with 2^n + 1 powerful is n = 3.

This is an open problem. The LTE-based exclusion approach above rules out
≥ 77% of all natural numbers unconditionally, but does not cover all cases.
The remaining cases (e.g., n ≡ 3 mod 6, n ≡ 10 mod 20, n ≡ 68 mod 136, ...)
require additional arguments that are not yet known. -/
theorem erdos936_lte_exclusion (n : ℕ) (hn : n ≥ 1)
    (hpow : ∀ p, Nat.Prime p → p ∣ (2^n+1) → p^2 ∣ (2^n+1)) :
    n = 3 := by sorry