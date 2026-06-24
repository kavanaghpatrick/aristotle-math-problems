import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# 9 divides C(2^(k+1), 2^k) for k ≥ 3, k ∉ {6, 8}

This is an **open problem** from Holdum-Klausen-Rasmussen 2026 (arXiv:2601.09510).
They verify computationally for k ≤ 10^13 and prove the density of exceptional k is zero,
but the unconditional statement for all k > 8 remains open.

## Proof strategy

**Reduction (Kummer's theorem):** By `padicValNat_choose`, the 3-adic valuation of
C(2^(k+1), 2^k) equals the number of "carries" when adding 2^k + 2^k in base 3.
A carry at position i occurs iff 3^i ≤ 2 · (2^k mod 3^i). So 9 | C(2^(k+1), 2^k)
iff there are at least 2 such carries.

**Unconditionally proven infinite families** (via Kummer carry counting):
- k ≡ 3 (mod 6): carries at i=1,2 (2^k mod 3 = 2, 2^k mod 9 = 8)
- k ≡ 5 (mod 6): carries at i=1,2 (2^k mod 3 = 2, 2^k mod 9 = 5)
- k ≡ 7 (mod 18): carries at i=1,3 (2^k mod 3 = 2, 2^k mod 27 = 20)
- k ≡ 4 (mod 18): carries at i=2,3 (2^k mod 9 = 7, 2^k mod 27 = 16)
- k ≡ 10 (mod 18): carries at i=2,3 (2^k mod 9 = 7, 2^k mod 27 = 25)

Together these cover 50% of all residue classes (9/18).

**Finite verification:** k ∈ {3,...,20} \ {6,8} by `native_decide`.

**Open gap:** k > 20 in the remaining residue classes mod 18:
{0, 1, 2, 6, 8, 12, 13, 14, 16} (mod 18), excluding k ∈ {6, 8}.
-/

/-! ## Core infrastructure -/

/-- The 3-adic valuation of C(2^(k+1), 2^k) via Kummer carry counting. -/
lemma padicValNat_three_central_binom_pow (k : ℕ) (b : ℕ) (hb : Nat.log 3 (2 ^ (k + 1)) < b) :
    padicValNat 3 (Nat.choose (2 ^ (k + 1)) (2 ^ k)) =
      (Finset.Ico 1 b |>.filter fun i => 3 ^ i ≤ 2 ^ k % 3 ^ i + 2 ^ k % 3 ^ i).card := by
  rw [padicValNat_choose]
  exacts [by rw [show 2 ^ (k + 1) - 2 ^ k = 2 ^ k by rw [Nat.sub_eq_of_eq_add]; ring],
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _), hb]

/-- 9 divides n when its 3-adic valuation is at least 2. -/
lemma nine_dvd_of_padicVal_ge_two (n : ℕ) (hn : 0 < n) (hv : 2 ≤ padicValNat 3 n) :
    9 ∣ n := by
  rw [← Nat.factorization_le_iff_dvd] <;> norm_num
  · rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.factorization_pow]; norm_num; aesop
  · linarith

/-- C(2^(k+1), 2^k) > 0. -/
lemma central_binom_pow_pos (k : ℕ) : 0 < Nat.choose (2 ^ (k + 1)) (2 ^ k) :=
  Nat.choose_pos (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

/-
General method: given carries at two distinct positions ≥ 1, conclude 9 | C(2^(k+1), 2^k).
-/
lemma nine_dvd_central_binom_of_two_carries (k i j : ℕ)
    (hij : i ≠ j) (hi1 : 1 ≤ i) (hj1 : 1 ≤ j)
    (hci : 3 ^ i ≤ 2 ^ k % 3 ^ i + 2 ^ k % 3 ^ i)
    (hcj : 3 ^ j ≤ 2 ^ k % 3 ^ j + 2 ^ k % 3 ^ j) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      have h_card : (Finset.Ico 1 (k + 2)).filter (fun i => 3 ^ i ≤ 2 ^ k % 3 ^ i + 2 ^ k % 3 ^ i) ⊇ {i, j} := by
        simp_all +decide [ Finset.insert_subset_iff ];
        have h_exp : 3 ^ i ≤ 2 ^ (k + 1) ∧ 3 ^ j ≤ 2 ^ (k + 1) := by
          exact ⟨ by rw [ pow_succ' ] ; linarith [ Nat.mod_le ( 2 ^ k ) ( 3 ^ i ) ], by rw [ pow_succ' ] ; linarith [ Nat.mod_le ( 2 ^ k ) ( 3 ^ j ) ] ⟩;
        exact ⟨ Nat.lt_succ_of_le ( Nat.le_of_not_lt fun hi => by linarith [ Nat.pow_le_pow_left ( show 2 ≤ 3 by decide ) ( k + 1 ), Nat.pow_lt_pow_right ( show 1 < 3 by decide ) hi ] ), Nat.lt_succ_of_le ( Nat.le_of_not_lt fun hj => by linarith [ Nat.pow_le_pow_left ( show 2 ≤ 3 by decide ) ( k + 1 ), Nat.pow_lt_pow_right ( show 1 < 3 by decide ) hj ] ) ⟩;
      convert nine_dvd_of_padicVal_ge_two ( Nat.choose ( 2 ^ ( k + 1 ) ) ( 2 ^ k ) ) ( central_binom_pow_pos k ) _ using 1;
      rw [ padicValNat_three_central_binom_pow ];
      exact Finset.card_mono h_card |> le_trans ( by norm_num [ hij ] );
      refine' Nat.log_lt_of_lt_pow _ _;
      · positivity;
      · exact lt_of_lt_of_le ( pow_lt_pow_left₀ ( by decide ) ( by decide ) ( by linarith ) ) ( pow_le_pow_right₀ ( by decide ) ( by linarith ) )

/-! ## Residue class proofs -/

/-
k ≡ 3 (mod 6): carries at positions 1 and 2.
-/
theorem div9_mod6_eq3 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 6 = 3) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      -- Apply nine_dvd_central_binom_of_two_carries with i=1, j=2.
      apply nine_dvd_central_binom_of_two_carries k 1 2 (by norm_num) (by norm_num) (by norm_num); all_goals rw [ ← Nat.mod_add_div k 6, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 5 (mod 6): carries at positions 1 and 2.
-/
theorem div9_mod6_eq5 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 6 = 5) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      apply nine_dvd_central_binom_of_two_carries k 1 2;
      · norm_num;
      · norm_num;
      · norm_num;
      · rw [ ← Nat.mod_add_div k 6, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      · rw [ ← Nat.mod_add_div k 6, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 7 (mod 18): carries at positions 1 and 3.
-/
theorem div9_mod18_eq7 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 18 = 7) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      convert nine_dvd_central_binom_of_two_carries k 1 3 _ _ _ _ _ using 1 <;> norm_num; all_goals rw [ ← Nat.mod_add_div k 18, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 4 (mod 18): carries at positions 2 and 3.
-/
theorem div9_mod18_eq4 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 18 = 4) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      -- Apply the lemma with i=2 and j=3.
      apply nine_dvd_central_binom_of_two_carries k 2 3 (by norm_num) (by norm_num) (by norm_num); all_goals rw [ ← Nat.mod_add_div k 18, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 10 (mod 18): carries at positions 2 and 3.
-/
theorem div9_mod18_eq10 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 18 = 10) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      apply nine_dvd_central_binom_of_two_carries k 2 3; norm_num;
      · norm_num;
      · norm_num;
      · rw [ ← Nat.mod_add_div k 18, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      · rw [ ← Nat.mod_add_div k 18, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-! ## Finite verification -/

set_option maxHeartbeats 4000000000 in
/-- Finite verification for k ∈ {3,...,20} \ {6, 8}. -/
theorem div9_small (k : ℕ) (hk3 : 3 ≤ k) (hk6 : k ≠ 6) (hk8 : k ≠ 8)
    (hle : k ≤ 20) : 9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
  interval_cases k <;> first | omega | native_decide

/-! ## Mod 54 level proofs -/

/-
k ≡ 19 (mod 54): carries at positions 1 and 4.
-/
theorem div9_mod54_eq19 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 54 = 19) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      -- We'll use that $2^k \equiv 2 \pmod{3}$ and $2^k \equiv 56 \pmod{81}$ to show that there are carries at positions 1 and 4.
      have h_mod3 : 2 ^ k % 3 = 2 := by
        rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      have h_mod81 : 2 ^ k % 81 = 56 := by
        rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      have h_carries : 3 ^ 1 ≤ 2 ^ k % 3 ^ 1 + 2 ^ k % 3 ^ 1 ∧ 3 ^ 4 ≤ 2 ^ k % 3 ^ 4 + 2 ^ k % 3 ^ 4 := by
        norm_num [ h_mod3, h_mod81 ]
      exact nine_dvd_central_binom_of_two_carries k 1 4 (by norm_num) (by norm_num) (by norm_num) h_carries.left h_carries.right

/-
k ≡ 12 (mod 54): carries at positions 3 and 4.
-/
theorem div9_mod54_eq12 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 54 = 12) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      -- Let $i = 3$ and $j = 4$.
      have h_carries : 3 ^ 3 ≤ 2 ^ k % 3 ^ 3 + 2 ^ k % 3 ^ 3 ∧ 3 ^ 4 ≤ 2 ^ k % 3 ^ 4 + 2 ^ k % 3 ^ 4 := by
        rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      exact nine_dvd_central_binom_of_two_carries k 3 4 ( by decide ) ( by decide ) ( by decide ) h_carries.1 h_carries.2

/-
k ≡ 30 (mod 54): carries at positions 3 and 4.
-/
theorem div9_mod54_eq30 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 54 = 30) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      convert nine_dvd_central_binom_of_two_carries k 3 4 _ _ _ _ _ using 1;
      · norm_num;
      · native_decide +revert;
      · norm_num;
      · rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      · rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 31 (mod 54): carries at positions 1 and 4.
-/
theorem div9_mod54_eq31 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 54 = 31) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      apply nine_dvd_central_binom_of_two_carries k 1 4 (by decide) (by decide) (by decide); all_goals rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 32 (mod 54): carries at positions 3 and 4.
-/
theorem div9_mod54_eq32 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 54 = 32) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      -- Apply the lemma with i=3 and j=4.
      apply nine_dvd_central_binom_of_two_carries k 3 4 (by norm_num) (by norm_num) (by norm_num); all_goals rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 50 (mod 54): carries at positions 3 and 4.
-/
theorem div9_mod54_eq50 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 54 = 50) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      -- Apply the lemma with i=3 and j=4.
      apply nine_dvd_central_binom_of_two_carries k 3 4 (by norm_num) (by norm_num) (by norm_num); all_goals rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-
k ≡ 52 (mod 54): carries at positions 2 and 4.
-/
theorem div9_mod54_eq52 (k : ℕ) (_hk : 3 ≤ k) (hmod : k % 54 = 52) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
      convert nine_dvd_central_binom_of_two_carries k 2 4 _ _ _ _ _ using 1 <;> norm_num; all_goals rw [ ← Nat.mod_add_div k 54, hmod ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;

/-! ## Open content -/

/-- The open conjecture for residue classes not yet covered.
    Verified for k ≤ 10^13 (HKR 2026), unconditional proof unknown.
    Remaining open classes mod 54:
    {0, 1, 2, 6, 8, 13, 14, 16, 18, 20, 24, 26, 34, 36, 37, 38, 42, 44, 48, 49}. -/
theorem div9_open (k : ℕ) (hk : 3 ≤ k) (hk6 : k ≠ 6) (hk8 : k ≠ 8)
    (hmod3 : k % 6 ≠ 3) (hmod5 : k % 6 ≠ 5)
    (hmod18_7 : k % 18 ≠ 7) (hmod18_4 : k % 18 ≠ 4) (hmod18_10 : k % 18 ≠ 10)
    (hmod54_19 : k % 54 ≠ 19) (hmod54_12 : k % 54 ≠ 12) (hmod54_30 : k % 54 ≠ 30)
    (hmod54_31 : k % 54 ≠ 31) (hmod54_32 : k % 54 ≠ 32) (hmod54_50 : k % 54 ≠ 50)
    (hmod54_52 : k % 54 ≠ 52) :
    9 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by sorry

/-! ## Main theorem -/

/-- **OPEN PROBLEM.** For every k ≥ 3 with k ≠ 6, 8, 9 divides C(2^(k+1), 2^k).

Verified computationally for k ≤ 10^13 by Holdum-Klausen-Rasmussen 2026
(arXiv:2601.09510, Theorem 1.2). The remaining sorry in `div9_open` encapsulates
the open content — it covers k > 20 in 20 out of 54 residue classes (mod 54).

**What is proven unconditionally (sorry-free):**
- All k ≤ 20 (by `native_decide`)
- k ≡ 3, 5 (mod 6): carries at i = 1, 2
- k ≡ 7 (mod 18): carries at i = 1, 3
- k ≡ 4, 10 (mod 18): carries at i = 2, 3
- k ≡ 12, 30, 32, 50 (mod 54): carries at i = 3, 4
- k ≡ 19, 31 (mod 54): carries at i = 1, 4
- k ≡ 52 (mod 54): carries at i = 2, 4
These cover 34 out of 54 residue classes (≈ 63% of all k). -/
theorem central_binom_pow_two_div_9
    (k : Nat) (hk : 3 <= k) (hk6 : k != 6) (hk8 : k != 8) :
    9 ∣ Nat.choose (2^(k+1)) (2^k) := by
  have h6 : k ≠ 6 := by simp [bne_iff_ne] at hk6; exact hk6
  have h8 : k ≠ 8 := by simp [bne_iff_ne] at hk8; exact hk8
  by_cases hle : k ≤ 20
  · exact div9_small k hk h6 h8 hle
  · push_neg at hle
    -- Dispatch by residue class, from coarsest to finest
    by_cases hmod3 : k % 6 = 3
    · exact div9_mod6_eq3 k hk hmod3
    · by_cases hmod5 : k % 6 = 5
      · exact div9_mod6_eq5 k hk hmod5
      · by_cases h7 : k % 18 = 7
        · exact div9_mod18_eq7 k hk h7
        · by_cases h4 : k % 18 = 4
          · exact div9_mod18_eq4 k hk h4
          · by_cases h10 : k % 18 = 10
            · exact div9_mod18_eq10 k hk h10
            · -- Mod 54 cases
              by_cases h19 : k % 54 = 19
              · exact div9_mod54_eq19 k hk h19
              · by_cases h12 : k % 54 = 12
                · exact div9_mod54_eq12 k hk h12
                · by_cases h30 : k % 54 = 30
                  · exact div9_mod54_eq30 k hk h30
                  · by_cases h31 : k % 54 = 31
                    · exact div9_mod54_eq31 k hk h31
                    · by_cases h32 : k % 54 = 32
                      · exact div9_mod54_eq32 k hk h32
                      · by_cases h50 : k % 54 = 50
                        · exact div9_mod54_eq50 k hk h50
                        · by_cases h52 : k % 54 = 52
                          · exact div9_mod54_eq52 k hk h52
                          · exact div9_open k hk h6 h8 hmod3 hmod5 h7 h4 h10
                              h19 h12 h30 h31 h32 h50 h52