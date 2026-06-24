import Mathlib
import RequestProject.LucasU

/-!
# Lucas V-sequence and companion identities

The Lucas V-sequence `V_n(P, Q)` is defined by the recurrence
`V_0 = 2, V_1 = P, V_n = P * V_{n-1} - Q * V_{n-2}`.

When `α + β = P` and `α * β = Q`, we have `V_n = α^n + β^n`.
-/

/-- Lucas V-sequence: the companion recurrence `V_n = P·V_{n-1} - Q·V_{n-2}`. -/
def lucasV (P Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | (n + 2) => P * lucasV P Q (n + 1) - Q * lucasV P Q n

@[simp] lemma lucasV_zero (P Q : ℤ) : lucasV P Q 0 = 2 := rfl
@[simp] lemma lucasV_one (P Q : ℤ) : lucasV P Q 1 = P := rfl

lemma lucasV_succ_succ (P Q : ℤ) (n : ℕ) :
    lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl

/-
The closed form for V: `V_n = α^n + β^n`.
-/
lemma lucasV_eq_sum_pow {P Q : ℤ} {α β : ℂ}
    (hsum : (α + β : ℂ) = ↑P) (hprod : (α * β : ℂ) = ↑Q)
    (n : ℕ) :
    (lucasV P Q n : ℂ) = α ^ n + β ^ n := by
      induction' n using Nat.strongRecOn with n ih;
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ lucasV_succ_succ ];
      · norm_num;
      · rw [ ← hsum, ← hprod ] ; ring

/-
Key identity: `U_{2n} = U_n · V_n`.
-/
lemma lucasU_double (P Q : ℤ) (n : ℕ) :
    lucasU P Q (2 * n) = lucasU P Q n * lucasV P Q n := by
      -- We will prove this identity by induction on $n$.
      induction' n using Nat.strong_induction_on with n ih;
      rcases n with ( _ | _ | n ) <;> simp +decide [ *, Nat.mul_succ ];
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mul_succ, lucasU_succ_succ, lucasV_succ_succ ];
      · ring;
      · ring;
      · have H := ih ( n + 1 ) ( by linarith ) ; have H' := ih ( n + 2 ) ( by linarith ) ; simp_all +decide [ Nat.mul_succ, lucasU_succ_succ, lucasV_succ_succ ] ; ring;
        grind

/-
**Tripling formula**: `U_{3m} = U_m · (V_m² - Q^m)`.
    This factorization is the key structural identity for the k=3 case.
-/
lemma lucasU_triple (P Q : ℤ) (m : ℕ) :
    lucasU P Q (3 * m) = lucasU P Q m * (lucasV P Q m ^ 2 - Q ^ m) := by
      -- Use the closed forms to reduce to a complex identity.
      have h_closed_form : ∀ (P Q : ℤ) (α β : ℂ) (m : ℕ), (α + β = P) → (α * β = Q) → (α ≠ β) → (lucasU P Q (3 * m) : ℂ) = (lucasU P Q m : ℂ) * ((lucasV P Q m : ℂ) ^ 2 - Q ^ m) := by
        intros P Q α β m hsum hprod hne;
        rw [ lucasU_eq_div_sub hsum hprod hne, lucasU_eq_div_sub hsum hprod hne, lucasV_eq_sum_pow hsum hprod ];
        rw [ ← hprod ] ; ring;
      -- Choose specific values for α and β that satisfy the conditions.
      by_cases h_disc : (P : ℂ) ^ 2 - 4 * (Q : ℂ) ≠ 0;
      · convert h_closed_form P Q ( ( P + ( P^2 - 4 * Q ) ^ ( 1/2 : ℂ ) ) / 2 ) ( ( P - ( P^2 - 4 * Q ) ^ ( 1/2 : ℂ ) ) / 2 ) m _ _ _ using 1 <;> norm_num [ ← Complex.ofReal_inj ] at *;
        · norm_cast;
        · ring;
        · ring_nf; norm_num [ ← Complex.cpow_nat_mul, h_disc ] ; ring;
        · norm_num [ sub_eq_add_neg, h_disc ];
          rw [ eq_neg_iff_add_eq_zero ] ; ring_nf at * ; aesop;
      · -- When $P^2 - 4Q = 0$, we have $P = 2\alpha$ and $Q = \alpha^2$ for some $\alpha$.
        obtain ⟨α, hα⟩ : ∃ α : ℤ, P = 2 * α ∧ Q = α ^ 2 := by
          norm_cast at h_disc; simp_all +decide [ sub_eq_iff_eq_add ] ;
          exact ⟨ P / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by simpa +decide [ parity_simps ] using congr_arg Even h_disc ) ) ], by cases abs_cases P <;> nlinarith [ Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by simpa +decide [ parity_simps ] using congr_arg Even h_disc ) ) ] ⟩;
        -- By definition of Lucas sequences, we know that $U_n(2\alpha, \alpha^2) = n\alpha^{n-1}$ and $V_n(2\alpha, \alpha^2) = 2\alpha^n$.
        have h_lucas_def : ∀ n : ℕ, lucasU (2 * α) (α ^ 2) n = n * α ^ (n - 1) ∧ lucasV (2 * α) (α ^ 2) n = 2 * α ^ n := by
          intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ lucasU_succ_succ, lucasV_succ_succ ] ;
          constructor <;> cases n <;> norm_num [ pow_succ' ] <;> ring;
        rcases m with ( _ | m ) <;> simp_all +decide [ pow_succ, mul_assoc, mul_left_comm, mul_comm ] ; ring;
        rw [ show 3 + m * 3 - 1 = 2 + m * 3 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;