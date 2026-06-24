import Mathlib

/-- A natural number `n` is powerful iff for every prime `p` dividing `n`, `p^2` also divides `n`. -/
def Nat.Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

/-! ## Pell sequence for x² - 8y² = 1

We define the Pell recurrence as a pair-valued function:
- (x₀, y₀) = (3, 1)
- (x_{k+1}, y_{k+1}) = (3·x_k + 8·y_k, x_k + 3·y_k)

This generates all positive solutions to x² - 8y² = 1.
-/

/-- The k-th positive Pell solution (x, y) to x² - 8y² = 1. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | k + 1 =>
    let (x, y) := pellPair k
    (3 * x + 8 * y, x + 3 * y)

/-- The x-component of the k-th positive Pell solution. -/
def pellX (k : ℕ) : ℕ := (pellPair k).1

/-- The y-component of the k-th positive Pell solution. -/
def pellY (k : ℕ) : ℕ := (pellPair k).2

lemma pellPair_zero : pellPair 0 = (3, 1) := rfl

lemma pellPair_succ (k : ℕ) :
    pellPair (k + 1) = (3 * pellX k + 8 * pellY k, pellX k + 3 * pellY k) := by
  simp [pellPair, pellX, pellY]

lemma pellX_zero : pellX 0 = 3 := rfl
lemma pellY_zero : pellY 0 = 1 := rfl

lemma pellX_succ (k : ℕ) : pellX (k + 1) = 3 * pellX k + 8 * pellY k := by
  simp [pellX, pellY, pellPair]

lemma pellY_succ (k : ℕ) : pellY (k + 1) = pellX k + 3 * pellY k := by
  simp [pellX, pellY, pellPair]

/-! ### Basic properties of the Pell sequence -/

/-
The Pell identity: pellX(k)² = 8 · pellY(k)² + 1.
-/
lemma pell_identity (k : ℕ) : pellX k ^ 2 = 8 * pellY k ^ 2 + 1 := by
  induction' k with k ih;
  · rfl;
  · rw [ pellX_succ, pellY_succ ] ; linarith;

/-
pellY is positive for all k.
-/
lemma pellY_pos (k : ℕ) : 0 < pellY k := by
  induction' k with k ih <;> [ norm_num [ pellY_zero ] ; rw [ pellY_succ ] ];
  grind

/-
pellX is at least 3 for all k.
-/
lemma pellX_ge_three (k : ℕ) : 3 ≤ pellX k := by
  induction' k with k ih;
  · rfl;
  · linarith [ pellX_succ k, pellY_pos k ]

/-
pellY(k) < pellY(k+1) for all k.
-/
lemma pellY_lt_succ (k : ℕ) : pellY k < pellY (k + 1) := by
  rw [ pellY_succ ];
  linarith [ pellX_ge_three k, pellY_pos k ]

/-- pellY is strictly monotone. -/
lemma pellY_strictMono : StrictMono pellY :=
  strictMono_nat_of_lt_succ pellY_lt_succ

/-! ### Powerfulness lemmas -/

/-
Any perfect square is powerful.
-/
lemma Nat.Powerful.sq (n : ℕ) : Nat.Powerful (n ^ 2) := by
  intro p hp;
  exact pow_dvd_pow_of_dvd ( Nat.Prime.dvd_of_dvd_pow ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ) 2

/-
8 * y² is powerful for any positive y.
-/
lemma powerful_eight_mul_sq (y : ℕ) (_hy : 0 < y) : Nat.Powerful (8 * y ^ 2) := by
  intro p;
  by_cases hp : p = 2 <;> simp_all +decide [ Nat.Prime.dvd_mul ];
  · exact fun _ => dvd_mul_of_dvd_left ( by decide ) _;
  · intro pp dp; rcases dp with ( dp | dp ) <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
    · exact False.elim <| dp <| pp.coprime_iff_not_dvd.mpr fun h => hp <| by have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> trivial;
    · exact fun _ => dvd_mul_of_dvd_right ( pow_dvd_pow_of_dvd ( pp.dvd_iff_not_coprime.mpr dp ) 2 ) _

/-! ### Main theorem -/

theorem powerful_consecutive_pairs_unbounded (N : ℕ) :
    ∃ n, N < n ∧ Nat.Powerful n ∧ Nat.Powerful (n + 1) := by
  -- Use k large enough so that 8 * pellY(k)² > N
  -- Then n := 8 * pellY(k)² works: n is powerful, n+1 = pellX(k)² is powerful
  -- Set n = 8 * pellY(N)^2. We need to show that n > N.
  use 8 * pellY N ^ 2;
  refine' ⟨ _, _, _ ⟩;
  · nlinarith [ show pellY N ≥ N + 1 from Nat.recOn N ( by norm_num [ pellY_zero ] ) fun n ihn => by linarith [ ihn, pellY_lt_succ n ] ];
  · exact powerful_eight_mul_sq _ ( pellY_pos _ );
  · rw [ show 8 * pellY N ^ 2 + 1 = pellX N ^ 2 by linarith [ pell_identity N ] ] ; exact Nat.Powerful.sq _