import Mathlib

/-!
# Erdős Problem 938 — Consecutive Powerful 3-APs

A natural number `n` is **powerful** (also called *squarefull*) if every prime
factor of `n` appears with exponent ≥ 2.

Erdős Problem 938 asks: is the set of indices `k` such that the `k`-th,
`(k+1)`-th, and `(k+2)`-th powerful numbers form an arithmetic progression
finite?

## Status

This is an **open problem**. The main theorem `erdos_938` is left as `sorry`.
We prove several unconditional supporting lemmas.
-/

open scoped BigOperators
open Nat

set_option maxHeartbeats 800000

/-! ### Definition of powerful numbers -/

/-- A natural number is **powerful** (squarefull) if for every prime `p`
dividing `n`, we have `p^2 ∣ n`. By convention `0` is not powerful. -/
def Nat.Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- `1` is powerful. -/
theorem Nat.Powerful.one : Nat.Powerful 1 := by
  refine ⟨by omega, fun p hp hd => ?_⟩
  have h1 := hp.one_le
  have h2 := Nat.le_of_dvd (by omega) hd
  have : p = 1 := by omega
  subst this; exact absurd hp Nat.not_prime_one

/-
Every perfect square `n^2` with `n ≥ 1` is powerful.
-/
theorem Nat.Powerful.sq {n : ℕ} (hn : 0 < n) : Nat.Powerful (n ^ 2) := by
  exact ⟨ by positivity, fun p pp dp => dvd_trans ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2 ) ( dvd_refl _ ) ⟩

/-
There are infinitely many powerful numbers (since all squares ≥ 1 are powerful).
-/
theorem Nat.Powerful.infinite : Set.Infinite {n : ℕ | Nat.Powerful n} := by
  exact Set.infinite_of_forall_exists_gt fun n => ⟨ ( n + 1 ) ^ 2, Nat.Powerful.sq n.succ_pos, by nlinarith ⟩

/-! ### Arithmetic progressions -/

/-- Three natural numbers form a 3-term arithmetic progression. -/
def IsAP3 (a b c : ℕ) : Prop := 2 * b = a + c

/-! ### Van Doorn family (Lemma L2) -/

/-
If `x^2 - 343 * y^2 = 2` with `x ≥ 3`, then `((x-2)^2, (x-1)^2, 343 * y^2)`
is a 3-term AP of powerful numbers.

**Proof sketch:** The AP condition `2*(x-1)^2 = (x-2)^2 + 343*y^2` reduces to
`x^2 - 343*y^2 = 2` by expanding. The first two terms are squares hence powerful.
The third term `343*y^2 = 7^3 * y^2` is powerful since 7 appears to power ≥ 3
and every prime in `y^2` appears to power ≥ 2.
-/
theorem van_doorn_family_ap (x y : ℕ) (hx : x ≥ 3)
    (hpell : x ^ 2 = 343 * y ^ 2 + 2) (_hy : 0 < y) :
    IsAP3 ((x - 2) ^ 2) ((x - 1) ^ 2) (343 * y ^ 2) := by
      rcases x with ( _ | _ | x ) <;> simp_all +arith +decide [ IsAP3 ] ; linarith

theorem van_doorn_family_powerful_left (x : ℕ) (hx : x ≥ 3) :
    Nat.Powerful ((x - 2) ^ 2) :=
  Nat.Powerful.sq (by omega)

theorem van_doorn_family_powerful_mid (x : ℕ) (hx : x ≥ 3) :
    Nat.Powerful ((x - 1) ^ 2) :=
  Nat.Powerful.sq (by omega)

/-
`343 * y^2 = 7^3 * y^2` is powerful for `y > 0`.
-/
theorem van_doorn_family_powerful_right (y : ℕ) (hy : 0 < y) :
    Nat.Powerful (343 * y ^ 2) := by
      refine' ⟨ by positivity, _ ⟩;
      intro p pp dp; rw [ Nat.Prime.dvd_mul pp ] at dp; rcases dp with ( dp | dp ) <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
      · -- Since $p$ is prime and divides $343$, it must be that $p = 7$.
        have hp : p = 7 := by
          exact not_not.mp fun h => dp <| pp.coprime_iff_not_dvd.mpr fun h' => h <| by have := Nat.le_of_dvd ( by decide ) h'; interval_cases p <;> norm_num at *;
        subst hp
        norm_num at *;
        exact dvd_mul_of_dvd_left ( by decide ) _;
      · exact dvd_mul_of_dvd_right ( pow_dvd_pow_of_dvd ( pp.dvd_iff_not_coprime.mpr dp ) 2 ) _

/-! ### Pell equation (Lemma L3) -/

/-- The first solution to `x^2 - 343 * y^2 = 2`. -/
theorem pell_first_solution : 11427 ^ 2 = 343 * 617 ^ 2 + 2 := by norm_num

/-- The fundamental solution to `x^2 - 343 * y^2 = 1`. -/
theorem pell_fundamental : 130576328 ^ 2 = 343 * 7050459 ^ 2 + 1 := by norm_num

/-! ### Main conjecture (OPEN) -/

/-- **Erdős Problem 938 (OPEN CONJECTURE).**
The set of indices `k` such that the `k`-th, `(k+1)`-th, and `(k+2)`-th
powerful numbers form a 3-term arithmetic progression is finite.

This is an open problem. The computational evidence below 10^10 finds exactly
six such triples. Whether the set is truly finite is unknown. -/
theorem erdos_938 : {P : Finset ℕ | (∃ a d, d > 0 ∧ P = {a, a + d, a + 2 * d}) ∧ ∃ k,
    P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
         Nat.nth Nat.Powerful (k+2)}}.Finite := by
  sorry