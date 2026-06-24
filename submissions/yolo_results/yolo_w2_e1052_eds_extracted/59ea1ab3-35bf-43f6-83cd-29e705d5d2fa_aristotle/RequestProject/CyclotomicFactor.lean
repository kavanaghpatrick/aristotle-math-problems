import Mathlib
import RequestProject.LucasU
import RequestProject.LucasV

/-!
# Divisibility properties of Lucas sequences

Key algebraic properties of the Lucas U-sequence relevant to the primitive
divisor problem.
-/

/-- The algebraic divisibility property: `d ∣ n → U_d ∣ U_n` for Lucas sequences. -/
lemma lucasU_dvd_of_dvd (P Q : ℤ) (d n : ℕ) (hd : d ∣ n) :
    lucasU P Q d ∣ lucasU P Q n := by
  by_contra h
  have h_ind : ∀ k : ℕ, 1 ≤ k → lucasU P Q d ∣ lucasU P Q (d * k) := by
    intro k hk; induction hk <;> simp_all +decide [Nat.mul_succ, lucasU_succ_succ]
    rename_i k hk ih
    have h_recurrence :
        ∀ m n : ℕ,
          m ≥ 1 →
            n ≥ 1 →
              lucasU P Q (m + n) =
                lucasU P Q m * lucasU P Q (n + 1) - Q * lucasU P Q (m - 1) * lucasU P Q n := by
      intros m n hm hn
      induction' n with n ih generalizing m <;>
        simp_all +decide [Nat.mul_succ, lucasU_succ_succ]
      rcases n with (_ | n) <;> simp_all +decide [Nat.succ_eq_add_one, add_assoc]
      · cases m <;> simp_all +decide [lucasU_succ_succ]; ring
      · convert ih (m + 1) (by linarith) using 1; ring
        cases m <;> simp_all +decide [lucasU_succ_succ]; ring
    rw [h_recurrence] <;> norm_num [ih]
    · exact dvd_sub (dvd_mul_of_dvd_left ih _) (dvd_mul_left _ _)
    · exact Nat.mul_pos (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero (by aesop_cat))) hk
    · exact Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero (by aesop_cat))
  exact h (by obtain ⟨k, rfl⟩ := hd; exact if hk : 1 ≤ k then h_ind k hk else by aesop)

/-- Addition formula for Lucas U: `U_{m+n} = U_m · U_{n+1} - Q · U_{m-1} · U_n`
    for `m ≥ 1, n ≥ 1`. -/
lemma lucasU_add (P Q : ℤ) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    lucasU P Q (m + n) =
      lucasU P Q m * lucasU P Q (n + 1) - Q * lucasU P Q (m - 1) * lucasU P Q n := by
  revert m n
  intros m n hm hn
  have h_ind :
      ∀ k : ℕ,
        lucasU P Q (m + k) =
          lucasU P Q m * lucasU P Q (k + 1) - Q * lucasU P Q (m - 1) * lucasU P Q k := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    rcases k with (_ | _ | k) <;> simp_all +decide [Nat.add_comm m]
    · rcases m with (_ | _ | m) <;> simp_all +decide [Nat.add_comm 1, lucasU_succ_succ]
      ring
    · have := ih k (by linarith); have := ih (k + 1) (by linarith)
      simp_all +decide [add_right_comm, lucasU_succ_succ]; ring
  exact h_ind n

/-
**Determinant identity**: `U_n² - U_{n+1} · U_{n-1} = Q^{n-1}` for `n ≥ 1`.
    This is the determinant of the matrix `M^n` where `M = [[P, -Q], [1, 0]]`.
-/
lemma lucasU_det_identity (P Q : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    lucasU P Q n ^ 2 - lucasU P Q (n + 1) * lucasU P Q (n - 1) = Q ^ (n - 1) := by
      induction' hn with n hn ih;
      · simp +decide [ lucasU ];
      · rcases n <;> simp_all +decide [ pow_succ, lucasU_succ_succ ] ; ring_nf at *;
        linear_combination' ih * Q

/-
If `p ∣ U_n` and `p ∣ U_{n+1}` and `gcd(p, Q) = 1`, then `p = 1`.
    Equivalently: consecutive Lucas terms share no prime factors coprime to Q.
-/
lemma lucasU_consecutive_coprime (P Q : ℤ) (n : ℕ) (hn : 1 ≤ n)
    (p : ℕ) (hp : p.Prime) (hpQ : ¬ (p : ℤ) ∣ Q)
    (h1 : (p : ℤ) ∣ lucasU P Q n) (h2 : (p : ℤ) ∣ lucasU P Q (n + 1)) :
    False := by
      have := lucasU_det_identity P Q n hn;
      exact hpQ ( Int.Prime.dvd_pow' hp <| this ▸ dvd_sub ( dvd_pow h1 two_ne_zero ) ( dvd_mul_of_dvd_left h2 _ ) )

/-
Subtraction step: if `p ∣ U_m` and `p ∣ U_n` and `n ≤ m` and `p ∤ Q`,
    then `p ∣ U_{m - n}`.
-/
lemma lucasU_dvd_sub (P Q : ℤ) (p : ℕ) (hp : p.Prime)
    (hpQ : ¬ (p : ℤ) ∣ Q)
    (m n : ℕ) (hmn : n ≤ m) (hn_pos : 0 < n) (hm_pos : 0 < m)
    (hm : (p : ℤ) ∣ lucasU P Q m) (hn : (p : ℤ) ∣ lucasU P Q n) :
    (p : ℤ) ∣ lucasU P Q (m - n) := by
      by_cases h_cases : m = n;
      · aesop;
      · -- Write m = (m-n) + n. By lucasU_add (with m-n and n, both ≥ 1 when m > n):
        have h_add : lucasU P Q m = lucasU P Q (m - n) * lucasU P Q (n + 1) - Q * lucasU P Q (m - n - 1) * lucasU P Q n := by
          convert lucasU_add P Q ( m - n ) n ( Nat.sub_pos_of_lt ( lt_of_le_of_ne hmn ( Ne.symm h_cases ) ) ) hn_pos using 1 ; rw [ Nat.sub_add_cancel hmn ];
        haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
        have := @lucasU_consecutive_coprime P Q n hn_pos p hp;
        simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ]

/-
The "rank of apparition" (entry point) property: if `p ∣ U_n` and `p ∣ U_m`
    and `gcd(p, Q) = 1`, then `p ∣ U_{gcd(m,n)}`.
    Combined with `lucasU_dvd_of_dvd`, this means the set `{n : ℕ | p ∣ U_n}`
    is either {0} or `{k * rank(p) | k ∈ ℕ}`.
-/
lemma lucasU_dvd_gcd_of_dvd (P Q : ℤ) (p : ℕ) (hp : p.Prime)
    (hpQ : ¬ (p : ℤ) ∣ Q)
    (m n : ℕ) (hm : (p : ℤ) ∣ lucasU P Q m) (hn : (p : ℤ) ∣ lucasU P Q n) :
    (p : ℤ) ∣ lucasU P Q (Nat.gcd m n) := by
      induction' m using Nat.strong_induction_on with m ih generalizing n;
      induction' n using Nat.strong_induction_on with n ih';
      rcases lt_trichotomy m n with ( h | rfl | h );
      · by_cases hm_zero : m = 0;
        · aesop;
        · convert ih' ( n - m ) ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.pos_of_ne_zero hm_zero ) ) _ using 1;
          · rw [ Nat.gcd_sub_self_right h.le ];
          · convert lucasU_dvd_sub P Q p hp hpQ n m ( by linarith ) ( Nat.pos_of_ne_zero hm_zero ) ( Nat.pos_of_ne_zero ( by aesop ) ) hn hm using 1;
      · aesop;
      · grind