import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# Erdős Problem 938 — Finitely many 3-APs of consecutive powerful numbers

A natural number `n ≥ 1` is **powerful** (also called squarefull) if every prime
factor of `n` appears with exponent ≥ 2. Equivalently, `n` can be written as
`a² b³` with `b` squarefree (Golomb 1970).

Erdős asked: are there only finitely many indices `k` such that the three
consecutive powerful numbers `n_k, n_{k+1}, n_{k+2}` form an arithmetic
progression?

**Status: OPEN.** No unconditional finiteness proof is known as of 2025.
Chan (2022, arXiv:2210.00281) proves finiteness conditionally on the ABC
conjecture: under ABC, for any 3-AP `(n, n+d, n+2d)` of powerful integers,
`d ≫ n^{1/2 - ε}`, which combined with the gap bound for consecutive powerful
numbers forces only finitely many solutions.

## Proof landscape

Several approaches have been explored:

1. **CM elliptic curve approach (FALSIFIED):** The curve `E_d : y² = x(x+d)(x+2d)`
   has `j = 1728` and CM by `ℤ[i]`. However, the product `n(n+d)(n+2d)` of three
   powerful numbers in AP need not be a perfect square. Concrete counterexample:
   `(1728, 1764, 1800)` has product `1728 · 1764 · 1800 = 2¹¹ · 3⁷ · 5² · 7²`,
   which has odd exponents on 2 and 3.

2. **Pell-system approach (INCOMPLETE):** Writing `n_k = a_k² b_k³` with `b_k`
   squarefree (Golomb parametrization), the AP condition becomes
   `2a₂²b₂³ = a₁²b₁³ + a₃²b₃³`. Heath-Brown (1988) constructs infinitely many
   consecutive powerful *pairs* via Pell equations, but extending to triples
   generates a system of two Pell-type equations whose simultaneous solutions
   are expected (but not proved) to be finite.

3. **ABC conditional (Chan 2022):** Under ABC, `d ≫ n^{1/2-ε}` for any 3-AP
   `(n, n+d, n+2d)` of powerful numbers. Combined with the elementary gap bound
   for consecutive powerful numbers, this forces finiteness.
-/

/-- A natural number is **powerful** (squarefull) if `n ≥ 1` and for every prime
`p` dividing `n`, we have `p² ∣ n`. -/
def Nat.Powerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A set `S ⊆ ℕ` forms an arithmetic progression of length `len` if there
exist `a` and `d > 0` such that `S = {a, a+d, a+2d, …, a+(len-1)d}`. -/
def Set.IsAPOfLength (S : Set ℕ) (len : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ S = (Finset.image (fun i => a + i * d) (Finset.range len) : Set ℕ)

-- ============================================================================
-- Auxiliary lemmas
-- ============================================================================

/-- 1 is powerful. -/
theorem Nat.Powerful.one : Nat.Powerful 1 := by
  refine ⟨le_refl 1, fun p hp hd => ?_⟩
  have := hp.one_lt
  have := Nat.le_of_dvd one_pos hd
  omega

/-- Every perfect square ≥ 1 is powerful. -/
theorem Nat.Powerful.sq {n : ℕ} (hn : 1 ≤ n) : Nat.Powerful (n ^ 2) :=
  ⟨Nat.one_le_pow _ _ hn, fun p pp dp =>
    dvd_trans (pow_dvd_pow_of_dvd (pp.dvd_of_dvd_pow dp) _) (dvd_refl _)⟩

/-- The product of two powerful numbers is powerful. -/
theorem Nat.Powerful.mul {m n : ℕ} (hm : Nat.Powerful m) (hn : Nat.Powerful n) :
    Nat.Powerful (m * n) := by
  unfold Nat.Powerful at hm hn ⊢
  constructor
  · nlinarith
  · simp_all +decide [Nat.Prime.dvd_mul]
    rintro p pp (h | h)
    · exact dvd_mul_of_dvd_left (hm.2 p pp h) _
    · exact dvd_mul_of_dvd_right (hn.2 p pp h) _

/-- There are infinitely many powerful numbers. -/
theorem Nat.Powerful.infinite : (setOf Nat.Powerful).Infinite :=
  Set.infinite_of_forall_exists_gt fun n =>
    ⟨(n + 1) ^ 2, Nat.Powerful.sq (Nat.succ_pos _), by nlinarith⟩

-- ============================================================================
-- Verified 3-AP examples
-- ============================================================================

/-- 1728 = 2⁶ · 3³ is powerful. -/
theorem powerful_1728 : Nat.Powerful 1728 :=
  ⟨by norm_num, fun p pp dp => by
    have := Nat.le_of_dvd (by norm_num) dp; interval_cases p <;> norm_num at *⟩

/-- 1764 = 2² · 3² · 7² is powerful. -/
theorem powerful_1764 : Nat.Powerful 1764 := by
  constructor <;> norm_num
  intro p pp dp; have := Nat.le_of_dvd (by decide) dp; interval_cases p <;> norm_num at *

/-- 1800 = 2³ · 3² · 5² is powerful. -/
theorem powerful_1800 : Nat.Powerful 1800 :=
  ⟨by norm_num, fun p pp dp => by
    have := Nat.le_of_dvd (by norm_num) dp; interval_cases p <;> norm_num at *⟩

/-- (1728, 1764, 1800) forms a 3-AP of powerful numbers with common
difference 36, demonstrating that such progressions exist. -/
theorem three_ap_example :
    Set.IsAPOfLength ({1728, 1764, 1800} : Set ℕ) 3 ∧
    Nat.Powerful 1728 ∧ Nat.Powerful 1764 ∧ Nat.Powerful 1800 := by
  refine ⟨⟨1728, 36, by omega, ?_⟩, powerful_1728, powerful_1764, powerful_1800⟩
  ext x; simp; constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by omega, by ring⟩
    · exact ⟨1, by omega, by ring⟩
    · exact ⟨2, by omega, by ring⟩
  · rintro ⟨i, hi, rfl⟩; omega

-- ============================================================================
-- Main conjecture (OPEN)
-- ============================================================================

/-- **Erdős Problem 938 (OPEN).** There are only finitely many indices `k` such
that the three consecutive powerful numbers `n_k, n_{k+1}, n_{k+2}` form a
three-term arithmetic progression.

This is an open problem. Chan (2022) proves this under the ABC conjecture. -/
theorem erdos_938 :
    {P : Finset ℕ | Set.IsAPOfLength (P : Set ℕ) 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)}}.Finite := by sorry
