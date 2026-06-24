import Mathlib

/-!
# Lucas U-sequence and basic properties

The Lucas U-sequence `U_n(P, Q)` is defined by the recurrence
`U_0 = 0, U_1 = 1, U_n = P * U_{n-1} - Q * U_{n-2}`.

When `α + β = P` and `α * β = Q`, we have `U_n = (α^n - β^n) / (α - β)`.
-/

/-- Lucas U-sequence: the integer recurrence `U_n = P·U_{n-1} - Q·U_{n-2}`. -/
def lucasU (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => P * lucasU P Q (n + 1) - Q * lucasU P Q n

@[simp] lemma lucasU_zero (P Q : ℤ) : lucasU P Q 0 = 0 := rfl
@[simp] lemma lucasU_one (P Q : ℤ) : lucasU P Q 1 = 1 := rfl

lemma lucasU_succ_succ (P Q : ℤ) (n : ℕ) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := rfl

/-- `U_2 = P` -/
@[simp] lemma lucasU_two (P Q : ℤ) : lucasU P Q 2 = P := by
  simp [lucasU_succ_succ]

/-- `U_3 = P² - Q` -/
lemma lucasU_three (P Q : ℤ) : lucasU P Q 3 = P ^ 2 - Q := by
  simp [lucasU_succ_succ]
  ring

/-- For any `n ≥ 1`, `U_1 ∣ U_n`. Trivially true since `U_1 = 1`. -/
lemma lucasU_one_dvd (P Q : ℤ) (n : ℕ) : lucasU P Q 1 ∣ lucasU P Q n := by
  simp

/-
The closed form: when `α + β = P` and `α * β = Q` and `α ≠ β`,
    `U_n(P,Q) = (α^n - β^n) / (α - β)` in ℂ.
-/
lemma lucasU_eq_div_sub {P Q : ℤ} {α β : ℂ}
    (hsum : (α + β : ℂ) = ↑P) (hprod : (α * β : ℂ) = ↑Q) (hne : α ≠ β)
    (n : ℕ) :
    (lucasU P Q n : ℂ) = (α ^ n - β ^ n) / (α - β) := by
      induction' n using Nat.strongRecOn with n ih;
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ sub_eq_iff_eq_add' ];
      rw [ show lucasU P Q ( n + 2 ) = P * lucasU P Q ( n + 1 ) - Q * lucasU P Q n from rfl ] ; push_cast [ ← hsum, ← hprod, ih _ <| Nat.le_succ _, ih _ <| Nat.le_refl _, pow_succ' ] ; ring;