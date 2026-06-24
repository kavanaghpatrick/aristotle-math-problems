import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic
import RequestProject.CoveringFacts

/-!
# Infinitely many odd squarefree Sierpinski numbers

We prove that there are infinitely many positive integers k that are simultaneously
odd, squarefree, and Sierpinski (meaning k * 2^n + 1 is composite for every n ≥ 1).

## Proof strategy

We use the classical Selfridge covering system with primes S = {3, 5, 7, 13, 17, 241}.
By CRT, we find k₀ = 2931991 such that for every k ≡ k₀ (mod P) (where P = ∏S = 5592405),
the integer k * 2^n + 1 is divisible by some prime in S for every n ≥ 1.

Since k₀ is coprime to P, Dirichlet's theorem on primes in arithmetic progressions
gives infinitely many primes q ≡ k₀ (mod P). Each such prime q is:
- Odd (since q > 2)
- Squarefree (since primes are squarefree)
- Sierpinski (since q ≡ k₀ mod P and q > 241)
-/

private abbrev P : ℕ := 5592405
private abbrev k₀ : ℕ := 2931991

/-! ## Core modular arithmetic lemma -/

/-- If p ∣ (2^24 - 1) as integers, then 2^n % p = 2^(n%24) % p. -/
private lemma pow_two_mod_period (p n : ℕ) (_hp : 0 < p)
    (hperiod : (p : ℤ) ∣ (2 ^ 24 - 1 : ℤ)) :
    2 ^ n % p = 2 ^ (n % 24) % p := by
  rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
  zify at *
  rw [Int.ModEq.mul_left _
    (Int.ModEq.pow _ <| Int.ModEq.symm <| Int.modEq_of_dvd <| by aesop)]
  norm_num

/-- Core divisibility lifting: from a base covering check to all n and all k in the AP. -/
private lemma dvd_of_cover {p r : ℕ} (k n : ℕ) (_hp : 0 < p)
    (hdvd : p ∣ (k₀ * 2 ^ r + 1))
    (hperiod : (p : ℤ) ∣ (2 ^ 24 - 1 : ℤ))
    (hmod : n % 24 = r)
    (hk : k ≡ k₀ [MOD p]) : p ∣ (k * 2 ^ n + 1) := by
  simp_all +decide [← ZMod.natCast_eq_natCast_iff]
  rw [← ZMod.natCast_eq_zero_iff] at *
  simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← Nat.mod_add_div n 24, hmod]
  simp_all +decide [pow_add, pow_mul]
  erw [show (2 ^ 24 : ZMod p) = 1 by linear_combination' hperiod]
  aesop

/-! ## The covering gives a divisor for every n -/

/-- For k ≡ k₀ (mod P) and any n, a covering prime divides k * 2^n + 1. -/
private lemma exists_cover_dvd (k n : ℕ) (hk : k ≡ k₀ [MOD P]) :
    ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), p ∣ (k * 2 ^ n + 1) := by
  set r : Fin 24 := ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  obtain ⟨p, hp_mem, hp_div⟩ := covering_for_residue r
  have h_div : p ∣ (k * 2 ^ n + 1) :=
    dvd_of_cover k n
      (by fin_cases hp_mem <;> trivial)
      hp_div
      (by fin_cases hp_mem <;> trivial)
      rfl
      (hk.of_dvd <| by fin_cases hp_mem <;> trivial)
  exact ⟨p, hp_mem, h_div⟩

/-- k * 2^n + 1 is not prime when k ≡ k₀ (mod P), k > 241, n ≥ 1. -/
private lemma not_prime_of_cover (k n : ℕ) (hk : k ≡ k₀ [MOD P])
    (hbig : 241 < k) (hn : 0 < n) : ¬ Nat.Prime (k * 2 ^ n + 1) := by
  obtain ⟨p, hp_mem, hp_div⟩ := exists_cover_dvd k n hk
  intro H
  have := Nat.prime_dvd_prime_iff_eq
    (show Nat.Prime p from by fin_cases hp_mem <;> norm_num) H
  simp_all +decide
  rcases hp_mem with h | h | h | h | h | h <;>
    nlinarith [Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hn]

/-! ## Main theorem -/

private lemma k₀_isUnit : IsUnit ((k₀ : ℕ) : ZMod P) :=
  (ZMod.isUnit_iff_coprime 2931991 5592405).mpr rfl

theorem squarefree_odd_sierpinski_infinite :
    {k : ℕ | Odd k ∧ Squarefree k ∧ ∀ n : ℕ, 0 < n → ¬ Nat.Prime (k * 2 ^ n + 1)}.Infinite := by
  -- The set of primes q ≡ k₀ (mod P) is infinite by Dirichlet's theorem.
  have h_inf : {q : ℕ | Nat.Prime q ∧ (q : ZMod P) = (k₀ : ZMod P)}.Infinite := by
    convert Nat.infinite_setOf_prime_and_eq_mod k₀_isUnit using 1
  refine h_inf.mono ?_
  intro q ⟨hq_prime, hq_mod⟩
  have hq_mod_eq : q ≡ k₀ [MOD P] := by
    rwa [← ZMod.natCast_eq_natCast_iff]
  have hq_gt_241 : 241 < q :=
    not_le.mp fun h => by interval_cases q <;> exact absurd hq_mod_eq (by native_decide)
  exact ⟨hq_prime.odd_of_ne_two (by linarith),
         hq_prime.squarefree,
         fun n hn => not_prime_of_cover q n hq_mod_eq hq_gt_241 hn⟩
