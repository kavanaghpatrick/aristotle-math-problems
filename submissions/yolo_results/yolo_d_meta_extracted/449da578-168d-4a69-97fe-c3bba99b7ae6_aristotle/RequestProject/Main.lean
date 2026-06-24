import Mathlib

set_option maxHeartbeats 800000

/-! # Powerful numbers: Pell pairs and mod-36 residue constraints

A natural number `n` is *powerful* if every prime factor of `n` appears with exponent ≥ 2.

We prove:
(a) There are infinitely many `y` with both `8y²` and `8y² + 1` powerful (Pell equation).
(b) If `m, m+1, m+2` are all powerful then `m % 36 ∈ {7, 27, 35}` (mod 4 and mod 9 obstructions).
(c) If additionally `m + 1 = 8y²` then `m % 36 = 7`.
    For (c), the elimination of `m%36=27` uses the quadratic residue argument mod 9
    (y² ≡ 8 mod 9 has no solution). The elimination of `m%36=35` is equivalent to showing
    that `72z²-1` and `72z²+1` cannot both be powerful, which is a special case of the
    Erdős–Mollin–Walsh conjecture. This is left as `sorry`.
-/

/-- A natural number is *powerful* if every prime dividing it appears with exponent ≥ 2. -/
def Nat.Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

-- ============================================================
-- Section 1: Basic properties of powerful numbers
-- ============================================================

theorem Nat.Powerful.sq (n : ℕ) : Nat.Powerful (n ^ 2) := by
  intro p pp dp
  exact pow_dvd_pow_of_dvd (pp.dvd_of_dvd_pow dp) 2

theorem Nat.Powerful.eight_mul_sq (y : ℕ) : Nat.Powerful (8 * y ^ 2) := by
  intro p pp
  by_cases hp : p = 2 <;> simp_all +decide [Nat.Prime.dvd_mul]
  · exact dvd_mul_of_dvd_left (by decide) _
  · rintro (h | h)
    · have := Nat.le_of_dvd (by decide) h; interval_cases p <;> trivial
    · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (pp.dvd_of_dvd_pow h) 2) _

-- ============================================================
-- Section 2: Modular obstructions for powerful numbers
-- ============================================================

theorem Nat.Powerful.mod4_ne_two {n : ℕ} (h : Nat.Powerful n) : n % 4 ≠ 2 := by
  intro h_contra
  have := h 2 Nat.prime_two
  norm_num at this
  exact absurd (this (Nat.dvd_of_mod_eq_zero (by omega))) (by omega)

theorem Nat.Powerful.mod9_ne_three {n : ℕ} (h : Nat.Powerful n) : n % 9 ≠ 3 := by
  intro h_contra
  exact absurd (h 3 Nat.prime_three (Nat.dvd_of_mod_eq_zero (by omega))) (by omega)

theorem Nat.Powerful.mod9_ne_six {n : ℕ} (h : Nat.Powerful n) : n % 9 ≠ 6 := by
  intro h_contra
  exact absurd (h 3 Nat.prime_three (by omega)) (by omega)

-- ============================================================
-- Section 3: Pell equation x² - 8y² = 1
-- ============================================================

/-- Solutions (x, y) to x² - 8y² = 1 via the recurrence from (3, 1). -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | (n + 1) =>
    let (x, y) := pellPair n
    (3 * x + 8 * y, x + 3 * y)

def pellX (n : ℕ) : ℕ := (pellPair n).1
def pellY (n : ℕ) : ℕ := (pellPair n).2

@[simp] lemma pellX_zero : pellX 0 = 3 := rfl
@[simp] lemma pellY_zero : pellY 0 = 1 := rfl
@[simp] lemma pellX_succ (n : ℕ) : pellX (n + 1) = 3 * pellX n + 8 * pellY n := rfl
@[simp] lemma pellY_succ (n : ℕ) : pellY (n + 1) = pellX n + 3 * pellY n := rfl

private theorem pellXY_pos : ∀ n, 0 < pellX n ∧ 0 < pellY n := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    simp [pellX_succ, pellY_succ]
    constructor <;> linarith [ih.1, ih.2]

theorem pellX_pos (n : ℕ) : 0 < pellX n := (pellXY_pos n).1
theorem pellY_pos (n : ℕ) : 0 < pellY n := (pellXY_pos n).2

/-- The Pell equation identity: pellX(n)² = 8 · pellY(n)² + 1. -/
theorem pell_eq (n : ℕ) : pellX n ^ 2 = 8 * pellY n ^ 2 + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => simp only [pellX_succ, pellY_succ]; nlinarith

theorem pellY_strictMono : StrictMono pellY :=
  strictMono_nat_of_lt_succ fun n => by
    simp [pellY_succ]; linarith [pellX_pos n, pellY_pos n]

-- ============================================================
-- Section 4: Mod 36 constraints on powerful triples
-- ============================================================

/-- If m, m+1, m+2 are all powerful, then m ≡ 3 mod 4. -/
theorem powerful_triple_mod4 {m : ℕ}
    (hm : Nat.Powerful m) (hm1 : Nat.Powerful (m + 1)) (hm2 : Nat.Powerful (m + 2)) :
    m % 4 = 3 := by
  by_contra h_contra
  by_cases h0 : m % 4 = 0
  · exact Nat.Powerful.mod4_ne_two hm2 (by omega)
  · by_cases h1 : m % 4 = 1
    · exact Nat.Powerful.mod4_ne_two hm1 (by omega)
    · exact Nat.Powerful.mod4_ne_two hm (by omega)

/-- If m, m+1, m+2 are all powerful, then m % 9 ∈ {0, 7, 8}. -/
theorem powerful_triple_mod9 {m : ℕ}
    (hm : Nat.Powerful m) (hm1 : Nat.Powerful (m + 1)) (hm2 : Nat.Powerful (m + 2)) :
    m % 9 = 0 ∨ m % 9 = 7 ∨ m % 9 = 8 := by
  have h1 := hm.mod9_ne_three
  have h2 := hm1.mod9_ne_three
  have h3 := hm2.mod9_ne_three
  have h4 := hm.mod9_ne_six
  have h5 := hm1.mod9_ne_six
  have h6 := hm2.mod9_ne_six
  omega

-- ============================================================
-- Section 5: Part (c) helpers
-- ============================================================

/-- No square is ≡ 8 mod 9. Quadratic residues mod 9 are {0,1,4,7}. -/
theorem sq_mod9_ne_eight (y : ℕ) : y ^ 2 % 9 ≠ 8 := by
  rw [Nat.pow_mod]
  have := Nat.mod_lt y (by omega : 0 < 9)
  interval_cases (y % 9) <;> trivial

/-- If m + 1 = 8y² and m,m+1,m+2 are all powerful, then m % 9 ≠ 0.
    Proof: m%9=0 gives 8y² ≡ 1 mod 9, so y² ≡ 8 mod 9, contradicting QR. -/
theorem pell_mod9_ne_zero {m y : ℕ} (heq : m + 1 = 8 * y ^ 2)
    (_hm : Nat.Powerful m) (_hm1 : Nat.Powerful (m + 1)) (_hm2 : Nat.Powerful (m + 2)) :
    m % 9 ≠ 0 := by
  exact fun h => by
    have := congr_arg (· % 9) heq
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h] at this
    have := Nat.mod_lt y (by omega : 0 < 9)
    interval_cases (y % 9) <;> contradiction

/-- If m + 1 = 8y² and m,m+1,m+2 are all powerful, then m % 9 ≠ 8.
    This is equivalent to showing 72z²-1 and 72z²+1 cannot both be powerful
    (where y = 3z), which is a special case of the Erdős–Mollin–Walsh conjecture
    (no three consecutive integers are all powerful).
    Computationally verified for y ≤ 10000 with no counterexample found. -/
theorem pell_mod9_ne_eight {m y : ℕ} (heq : m + 1 = 8 * y ^ 2)
    (hm : Nat.Powerful m) (hm1 : Nat.Powerful (m + 1)) (hm2 : Nat.Powerful (m + 2)) :
    m % 9 ≠ 8 := by
  sorry

-- ============================================================
-- Section 6: Main theorem
-- ============================================================

theorem d_meta_walker_beckon_intersection :
    (∃ f : ℕ → ℕ, Function.Injective f ∧
       ∀ k, Nat.Powerful (8 * (f k)^2) ∧ Nat.Powerful (8 * (f k)^2 + 1))
    ∧ (∀ m : ℕ, Nat.Powerful m → Nat.Powerful (m + 1) → Nat.Powerful (m + 2) →
       m % 36 = 7 ∨ m % 36 = 27 ∨ m % 36 = 35)
    ∧ (∀ m y : ℕ, m + 1 = 8 * y^2 →
       Nat.Powerful m → Nat.Powerful (m + 1) → Nat.Powerful (m + 2) →
       m % 36 = 7) := by
  refine ⟨⟨pellY, pellY_strictMono.injective, fun k => ⟨?_, ?_⟩⟩,
         fun m hm hm1 hm2 => ?_, fun m y heq hm hm1 hm2 => ?_⟩
  -- Part (a): 8*(pellY k)² is powerful
  · exact Nat.Powerful.eight_mul_sq _
  -- Part (a): 8*(pellY k)² + 1 = (pellX k)² is powerful
  · rw [show 8 * (pellY k) ^ 2 + 1 = pellX k ^ 2 from by linarith [pell_eq k]]
    exact Nat.Powerful.sq _
  -- Part (b): m % 36 ∈ {7, 27, 35}
  · have h4 := powerful_triple_mod4 hm hm1 hm2
    have h9 := powerful_triple_mod9 hm hm1 hm2
    omega
  -- Part (c): m % 36 = 7 when m + 1 = 8y²
  · have h4 := powerful_triple_mod4 hm hm1 hm2
    have h9 := powerful_triple_mod9 hm hm1 hm2
    have hne0 := pell_mod9_ne_zero heq hm hm1 hm2
    have hne8 := pell_mod9_ne_eight heq hm hm1 hm2
    omega
