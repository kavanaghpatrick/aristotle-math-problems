import Mathlib

/-! # Powerful numbers and helper lemmas -/

set_option maxHeartbeats 800000

/-- A natural number is *powerful* if every prime factor appears with exponent ≥ 2. -/
def Nat.Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-
Every perfect square is powerful.
-/
lemma sq_powerful (n : ℕ) : Nat.Powerful (n ^ 2) := by
  intro p pp dp; rw [ pow_two ] at dp; simp_all +decide [ Nat.Prime.dvd_mul ] ;
  exact pow_dvd_pow_of_dvd dp 2

/-
7³ · y² is powerful for every natural number y.
-/
lemma powerful_7cube_mul_sq (y : ℕ) : Nat.Powerful (7 ^ 3 * y ^ 2) := by
  intro p pp; by_cases hp : p = 7 <;> simp_all +decide [ Nat.Prime.dvd_mul ] ;
  · exact dvd_mul_of_dvd_left ( by decide ) _;
  · rintro ( h | h );
    · have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> norm_num at *;
    · exact dvd_mul_of_dvd_right ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow h ) 2 ) _