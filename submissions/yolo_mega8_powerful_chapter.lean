/-
Copyright (c) 2026 Aristotle (Harmonic AI) consolidated chapter.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle / Mathlib community

# Powerful Numbers

A natural number `n` is *powerful* if every prime dividing `n` appears with
exponent at least `2`. Equivalently, by a theorem of Golomb (1970), `n` is
powerful iff `n = a^2 * b^3` for some `a, b ≥ 1` with `b` squarefree.

## Main results

* `Nat.Powerful` : the predicate stating `n > 0` and every prime factor of `n`
  appears to the second power.
* `Nat.powerful_iff_sq_mul_cube` (Golomb 1970) : `n.Powerful ↔ ∃ a b ≥ 1,
  Squarefree b ∧ n = a^2 * b^3`.
* `Nat.powerful_sq`, `Nat.powerful_cube` : positive squares and cubes are
  powerful.
* `Nat.no_powerful_between_consecutive` : the powerful numbers in
  consecutive-enumeration order have no element strictly between.
* `Nat.erdos_938_unconditional_upper_bound` (Erdős 938 unconditional) :
  any 3-AP `(n_k, n_{k+1}, n_{k+2})` of consecutively-enumerated powerful
  numbers has common difference `d < 2 √n_k + 2`.
* `Nat.erdos_364_mod36` (Beckon 2019) : if `n, n+1, n+2` are all powerful,
  then `n % 36 ∈ {7, 27, 35}`.
* `Nat.not_multiperfect_of_prime_card_divisors` : if `n > 1` has a prime
  number of divisors, then `n` is not multiperfect.
* `Nat.powerful_3AP_prime_once_not_dvd` (the D1 structural lemma) : in any
  powerful 3-AP `(n, n+d, n+2d)` with `v_p(d) = 1`, the prime `p` does not
  divide `n`.
* `Nat.powerful_3AP_squarefree_d_coprime` (chapter META) : if `d` is
  squarefree and `n, n+d, n+2d` are all powerful, then `Nat.Coprime n d`.

## References

* Solomon W. Golomb, *Powerful numbers*, Amer. Math. Monthly **77** (1970),
  848–852.
* P. Beckon, mod-36 obstruction for consecutive powerful triples (2019).
-/

import Mathlib

set_option maxHeartbeats 800000

open scoped Real BigOperators
open Finset Finsupp

namespace Nat

/-! ## Section 1: Definition and basic API -/

/-- A natural number `n` is *powerful* if `n > 0` and every prime factor of `n`
appears with exponent at least 2. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Every positive perfect square is powerful. -/
theorem powerful_sq {m : ℕ} (hm : 0 < m) : Powerful (m ^ 2) := by
  exact ⟨ pow_pos hm 2,
    fun p hp hpn =>
      dvd_trans (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hpn) 2)
                (pow_dvd_pow _ le_rfl) ⟩

/-- Every positive perfect cube is powerful. -/
theorem powerful_cube {m : ℕ} (hm : 0 < m) : Powerful (m ^ 3) := by
  refine ⟨ pow_pos hm 3, fun p hp hpn => ?_ ⟩
  have hp_dvd : p ∣ m := hp.dvd_of_dvd_pow hpn
  exact dvd_trans (pow_dvd_pow_of_dvd hp_dvd 2) (pow_dvd_pow _ (by omega))

/-- The constant `1` is powerful. -/
theorem powerful_one : Powerful 1 := by
  refine ⟨Nat.one_pos, fun p hp hpn => ?_⟩
  have : p = 1 := Nat.eq_one_of_dvd_one hpn
  exact absurd this hp.one_lt.ne'

/-- The set of powerful numbers is infinite. -/
theorem powerful_infinite : (setOf Powerful).Infinite :=
  Set.infinite_of_forall_exists_gt fun n =>
    ⟨ (n + 1) ^ 2, by simpa using powerful_sq (Nat.succ_pos _), by nlinarith ⟩

/-! ## Section 2: Golomb parametrization (T1)

A natural number `n ≥ 1` is powerful iff `n = a^2 * b^3` for some `a, b ≥ 1`
with `b` squarefree. (Golomb 1970.) -/

private theorem aux_arith (k : ℕ) (hk : 2 ≤ k) :
    k = 2 * ((k - 3 * (k % 2)) / 2) + 3 * (k % 2) := by
  omega

private theorem PowerfulOfFactorization (n : ℕ) (hn : 0 < n)
    (hf : ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n) : Powerful n := ⟨hn, hf⟩

/-- Powerful predicate (forgetful version, used in the Golomb proof and
the mod-36 result). -/
private def PowerfulNoPos (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

private theorem powerful_to_no_pos {n : ℕ} (h : Powerful n) : PowerfulNoPos n :=
  h.2

/-- Reverse direction of Golomb: `a^2 · b^3` with `b` squarefree, `a, b ≥ 1`,
is powerful. -/
theorem powerful_of_sq_mul_cube {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsq : Squarefree b) : Powerful (a ^ 2 * b ^ 3) := by
  refine ⟨ by positivity, fun p pp dp => ?_ ⟩
  rw [Nat.Prime.dvd_mul pp] at dp
  rcases dp with (dp | dp)
  · exact dvd_mul_of_dvd_left
      (pow_dvd_pow_of_dvd (pp.dvd_of_dvd_pow dp) 2) _
  · exact dvd_mul_of_dvd_right
      (dvd_trans
        (pow_dvd_pow_of_dvd (pp.dvd_of_dvd_pow dp) 2)
        (pow_dvd_pow _ (show (3 : ℕ) ≥ 2 by decide))) _

/-- Forward direction of Golomb: a powerful `n ≥ 1` decomposes as `a^2 * b^3`
with `b` squarefree. -/
theorem sq_mul_cube_of_powerful (n : ℕ) (hn : 1 ≤ n) (hp : Powerful n) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ Squarefree b ∧ n = a ^ 2 * b ^ 3 := by
  have hp' : PowerfulNoPos n := hp.2
  let b := ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1), p
  let a := ∏ p ∈ n.primeFactors, p ^ ((n.factorization p - 3 * (n.factorization p % 2)) / 2)
  have h_eq : n = a^2 * b^3 := by
    have h_factorization :
        ∀ p ∈ n.primeFactors,
          n.factorization p
            = 2 * ((n.factorization p - 3 * (n.factorization p % 2)) / 2)
              + 3 * (if n.factorization p % 2 = 1 then 1 else 0) := by
      intro p hp; split_ifs <;> simp_all +decide [Nat.div_mul_cancel]
      · have := hp' p hp.1 hp.2.1
        rcases k : n.factorization p with (_ | _ | _ | k) <;>
          simp_all +arith +decide [Nat.pow_succ']
        · rw [← sq] at this
          rw [← Nat.factorization_le_iff_dvd] at this <;> aesop
        · omega
      · grind
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self (by positivity : n ≠ 0)]
    simp +zetaDelta at *
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    rw [Finset.prod_filter]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    specialize h_factorization p
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
      (by positivity)
    rw [h_factorization]; ring
    cases Nat.mod_two_eq_zero_or_one (n.factorization p) <;> simp +decide [‹_›]
  refine ⟨a, b, ?_, ?_, ?_, h_eq⟩
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _
  · exact Finset.prod_pos fun p hp =>
      Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp |>.1)
  · refine Nat.squarefree_iff_prime_squarefree.mpr ?_
    intro p pp dp; simp +decide [← sq] at dp
    rw [Nat.Prime.pow_dvd_iff_le_factorization] at dp <;> norm_num at *
    · rw [Nat.factorization_prod] at dp <;> norm_num at *
      · rw [Finset.sum_eq_single p] at dp <;> norm_num at *
        · norm_num [pp.factorization] at dp
        · simp +contextual
        · intro h; contrapose! dp; simp +decide [pp.factorization] at *
          rw [Finset.sum_eq_zero] <;> norm_num
          intro q hq hqn hn hq'; rw [Nat.factorization_eq_zero_iff]
          exact Or.inr <| Or.inl <| by
            rintro H; have := Nat.prime_dvd_prime_iff_eq pp hq; simp_all +singlePass
      · exact fun x hx _ _ _ => hx.ne_zero
    · assumption
    · exact Finset.prod_ne_zero_iff.mpr fun q hq =>
        Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| Finset.filter_subset _ _ hq

/-- **Golomb (1970).** A natural number `n ≥ 1` is powerful iff `n = a^2 * b^3`
for some `a, b ≥ 1` with `b` squarefree. -/
theorem powerful_iff_sq_mul_cube (n : ℕ) (hn : 1 ≤ n) :
    Powerful n ↔ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ Squarefree b ∧ n = a ^ 2 * b ^ 3 := by
  refine ⟨ sq_mul_cube_of_powerful n hn, ?_ ⟩
  rintro ⟨a, b, ha, hb, hsq, rfl⟩
  exact powerful_of_sq_mul_cube ha hb hsq

/-! ## Section 3: Erdős 938 — gap structure for consecutively-enumerated powerfuls -/

/-- There is no powerful number strictly between two consecutively enumerated
powerful numbers. -/
theorem no_powerful_between_consecutive [DecidablePred Powerful]
    (k m : ℕ) (hm : Powerful m)
    (h1 : nth Powerful k < m) (h2 : m < nth Powerful (k + 1)) : False := by
  have h_count : (count Powerful m) > k := by
    contrapose! h1
    have := Nat.nth_monotone (show {n : ℕ | n.Powerful}.Infinite from powerful_infinite) h1
    aesop
  contrapose! h2
  have := Nat.nth_monotone (show {n : ℕ | n.Powerful}.Infinite from powerful_infinite) h_count
  aesop

/-- Any interval `[a, a + L)` with `L > 2 * √a + 1` contains a positive perfect square. -/
theorem interval_contains_square (a L : ℕ) (hL : 2 * Nat.sqrt a + 1 < L) :
    ∃ m : ℕ, 0 < m ∧ a < m ^ 2 ∧ m ^ 2 < a + L :=
  ⟨ Nat.sqrt a + 1, Nat.succ_pos _,
    by linarith [Nat.lt_succ_sqrt a],
    by linarith [Nat.sqrt_le a] ⟩

end Nat

/-- **Erdős 938 — Unconditional upper bound.**
If `n_k, n_{k+1}, n_{k+2}` are three consecutively enumerated powerful numbers
forming an arithmetic progression with common difference `d`, then
`(d : ℝ) < 2 √n_k + 2`. -/
theorem erdos_938_unconditional_upper_bound (k : ℕ) :
    let n0 := Nat.nth Nat.Powerful k
    let n1 := Nat.nth Nat.Powerful (k + 1)
    let n2 := Nat.nth Nat.Powerful (k + 2)
    n1 - n0 = n2 - n1 →
    ((n1 - n0 : ℝ) < 2 * Real.sqrt n0 + 2) := by
  intro n0 n1 n2 h_eq
  by_cases h_s : (Nat.sqrt n0 + 1)^2 < n2
  · by_cases h_case : n0 < (Nat.sqrt n0 + 1)^2 ∧ (Nat.sqrt n0 + 1)^2 < n1
    · contrapose! h_case
      intro h
      refine Nat.le_of_not_lt fun h' => ?_
      convert Nat.no_powerful_between_consecutive
        k ((Nat.sqrt n0 + 1) ^ 2) _ _ _ using 1
      · exact Classical.decPred _
      · exact Nat.powerful_sq (Nat.succ_pos _)
      · grobner
      · linarith
    · by_cases h_case2 : n1 < (Nat.sqrt n0 + 1)^2 ∧ (Nat.sqrt n0 + 1)^2 < n2
      · rw [← @Nat.cast_lt ℝ] at *; norm_num at *
        nlinarith only [Real.sqrt_nonneg n0,
          Real.sq_sqrt <| Nat.cast_nonneg n0,
          show (n0.sqrt :ℝ) ^ 2 ≤ n0 from mod_cast Nat.sqrt_le' n0,
          h_case, h_case2]
      · have h_s_eq_n1 : (Nat.sqrt n0 + 1)^2 = n1 := by
          have h_s_eq_n1' : n0 < (Nat.sqrt n0 + 1)^2 ∧ (Nat.sqrt n0 + 1)^2 < n2 :=
            ⟨Nat.lt_succ_sqrt' _, h_s⟩
          grind
        nlinarith only [Real.sqrt_nonneg n0,
          Real.sq_sqrt <| Nat.cast_nonneg n0,
          show (n0 :ℝ) ≥ (Nat.sqrt n0 :ℝ) ^ 2 by exact_mod_cast Nat.sqrt_le' n0,
          show (n1 :ℝ) = (Nat.sqrt n0 + 1) ^ 2 by exact_mod_cast h_s_eq_n1.symm]
  · have h2d_le : 2 * (n1 - n0) ≤ (Nat.sqrt n0 + 1)^2 - n0 := by omega
    generalize_proofs at *
    rw [Nat.le_sub_iff_add_le] at h2d_le
    · rw [← Nat.cast_sub
            (show n0 ≤ n1 from Nat.nth_monotone Nat.powerful_infinite (Nat.le_succ _))] at *
      norm_num at *
      nlinarith only [Real.sqrt_nonneg n0,
        Real.sq_sqrt <| Nat.cast_nonneg n0,
        (by norm_cast : (2 : ℝ) * (n1 - n0 : ℕ) + n0 ≤ (n0.sqrt + 1) ^ 2),
        (show (n0.sqrt : ℝ) ^ 2 ≤ n0 by norm_cast; linarith [Nat.sqrt_le n0])]
    · linarith [Nat.lt_succ_sqrt n0]

namespace Nat

/-! ## Section 4: Erdős 364 — mod-36 closure for consecutive powerful triples (Beckon 2019) -/

/-- If `x ≡ 2 (mod 4)` then `x` is not powerful: `2 ∣ x` but `4 ∤ x`. -/
lemma not_powerful_of_mod4_eq2 (x : ℕ) (h : x % 4 = 2) : ¬ Powerful x := by
  intro hpow
  have h4 : 4 ∣ x := by
    have := hpow.2 2 (by norm_num) (by omega : 2 ∣ x)
    norm_num at this; exact this
  omega

/-- If `x ≡ 3 (mod 9)` then `x` is not powerful: `3 ∣ x` but `9 ∤ x`. -/
lemma not_powerful_of_mod9_eq3 (x : ℕ) (h : x % 9 = 3) : ¬ Powerful x := by
  intro hpow
  have h9 : 9 ∣ x := by
    have := hpow.2 3 (by norm_num) (by omega : 3 ∣ x)
    norm_num at this; exact this
  omega

/-- If `x ≡ 6 (mod 9)` then `x` is not powerful: `3 ∣ x` but `9 ∤ x`. -/
lemma not_powerful_of_mod9_eq6 (x : ℕ) (h : x % 9 = 6) : ¬ Powerful x := by
  intro hpow
  have h9 : 9 ∣ x := by
    have := hpow.2 3 (by norm_num) (by omega : 3 ∣ x)
    norm_num at this; exact this
  omega

/-- **Erdős 364 — mod-36 closure (Beckon 2019).**
If `n`, `n + 1`, and `n + 2` are all powerful, then `n ≡ 7, 27, or 35 (mod 36)`. -/
theorem erdos_364_mod36
    (n : ℕ) (hn : Powerful n) (hn1 : Powerful (n + 1)) (hn2 : Powerful (n + 2)) :
    n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  -- Step 1: n ≡ 3 (mod 4)
  have hmod4 : n % 4 = 3 := by
    have h4 := Nat.mod_lt n (show 0 < 4 by norm_num)
    by_contra hne
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 := by omega
    rcases this with h | h | h
    · exact not_powerful_of_mod4_eq2 (n + 2) (by omega) hn2
    · exact not_powerful_of_mod4_eq2 (n + 1) (by omega) hn1
    · exact not_powerful_of_mod4_eq2 n h hn
  -- Step 2: n % 9 ∈ {0, 7, 8}
  have hmod9 : n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
    have h9 := Nat.mod_lt n (show 0 < 9 by norm_num)
    by_contra hne
    push_neg at hne
    have : n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 := by omega
    rcases this with h | h | h | h | h | h
    · exact not_powerful_of_mod9_eq3 (n + 2) (by omega) hn2
    · exact not_powerful_of_mod9_eq3 (n + 1) (by omega) hn1
    · exact not_powerful_of_mod9_eq3 n h hn
    · exact not_powerful_of_mod9_eq6 (n + 2) (by omega) hn2
    · exact not_powerful_of_mod9_eq6 (n + 1) (by omega) hn1
    · exact not_powerful_of_mod9_eq6 n h hn
  -- Step 3: CRT
  omega

/-! ## Section 5: Multiperfect bridge via prime number of divisors -/

/-- If `n > 1` and `σ₀(n)` (the number of divisors) is prime, then `n` is a prime power. -/
lemma isPrimePow_of_prime_card_divisors {n : ℕ} (hn : 1 < n)
    (hp : Nat.Prime (Nat.divisors n).card) : IsPrimePow n := by
  have h_card : n.divisors.card = ∏ p ∈ n.primeFactors, (Nat.factorization n p + 1) :=
    Nat.card_divisors hn.ne_bot
  have h_prime_factors : n.primeFactors.card = 1 := by
    induction h : n.primeFactors using Finset.induction <;>
      simp_all +decide [Nat.prime_mul_iff]
    simp_all +decide [Nat.factorization_eq_zero_iff, Finset.ext_iff]
    grind
  grind +suggestions

/-- **Multiperfect-σ₀ exclusion.** No `n > 1` with a prime number of divisors can be
multiperfect (i.e. `σ(n) = k · n` for some `k ≥ 2`). -/
theorem not_multiperfect_of_prime_card_divisors {n : ℕ} (hn : 1 < n)
    (hp : Nat.Prime (Nat.divisors n).card) :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ (Nat.divisors n).sum id = k * n := by
  have h_deficient : Nat.Deficient n :=
    IsPrimePow.deficient (isPrimePow_of_prime_card_divisors hn hp)
  simp_all +decide [Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.Deficient]
  exact fun x hx => by nlinarith

/-! ## Section 6: Structural coprimality (D1) and the chapter META -/

/-- **D1 structural lemma.** Suppose `n, n + d, n + 2d` are all powerful, and `p`
is a prime with `p ∣ d` but `p^2 ∤ d` (i.e. `v_p(d) = 1`). Then `p ∤ n`. -/
theorem powerful_3AP_prime_once_not_dvd
    (n d p : ℕ) (hd : 0 < d) (hp : p.Prime)
    (hpd : p ∣ d) (hpp : ¬ p^2 ∣ d)
    (h0 : Powerful n) (h1 : Powerful (n + d))
    (_h2 : Powerful (n + 2 * d)) :
    ¬ p ∣ n := by
  intro hpn
  -- Powerful n + p ∣ n ⇒ p^2 ∣ n.
  have hp2n : p ^ 2 ∣ n := h0.2 p hp hpn
  -- Powerful (n + d): since p ∣ d and p ∣ n, p ∣ n + d, hence p^2 ∣ n + d.
  have hp_nd : p ∣ n + d := dvd_add hpn hpd
  have hp2_nd : p ^ 2 ∣ n + d := h1.2 p hp hp_nd
  -- p^2 ∣ n + d and p^2 ∣ n ⇒ p^2 ∣ d, contradiction.
  have hp2_d : p ^ 2 ∣ d := by
    have hsub : p ^ 2 ∣ (n + d) - n := Nat.dvd_sub hp2_nd hp2n
    simpa [Nat.add_sub_cancel_left] using hsub
  exact hpp hp2_d

/-- **MEGA-8 chapter META — structural coprimality for squarefree-d powerful 3-APs.**
If `d > 0` is squarefree and `n, n + d, n + 2d` are all powerful, then `Nat.Coprime n d`. -/
theorem powerful_3AP_squarefree_d_coprime
    (n d : ℕ) (hd : 0 < d) (hsq : Squarefree d)
    (h0 : Powerful n) (h1 : Powerful (n + d))
    (h2 : Powerful (n + 2 * d)) :
    Nat.Coprime n d := by
  -- Coprime n d iff no prime divides both.
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  -- A common prime divisor exists.
  have hgcd_pos : 1 < Nat.gcd n d := by
    have : 0 < Nat.gcd n d := Nat.gcd_pos_of_pos_right n hd
    omega
  obtain ⟨p, hp_prime, hp_gcd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hgcd_pos).symm
  have hpn : p ∣ n := dvd_trans hp_gcd (Nat.gcd_dvd_left _ _)
  have hpd : p ∣ d := dvd_trans hp_gcd (Nat.gcd_dvd_right _ _)
  -- Squarefree d ⇒ ¬ (p^2 ∣ d).
  have hpp : ¬ p ^ 2 ∣ d := by
    intro h
    -- p * p ∣ d ⇒ p is a unit by Squarefree, contradicting Prime p.
    have hpp_mul : p * p ∣ d := by simpa [sq] using h
    exact hp_prime.not_unit (hsq p hpp_mul)
  -- Apply the D1 structural lemma.
  exact powerful_3AP_prime_once_not_dvd n d p hd hp_prime hpd hpp h0 h1 h2 hpn

/-! ## Section 7: Chapter bridge corollaries -/

/-- A powerful number factored as `a^2 * b^3` has all prime factors appearing in `a * b`. -/
theorem powerful_radical_eq_radical_param {n a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hsq : Squarefree b)
    (hn : n = a ^ 2 * b ^ 3) : ∀ p : ℕ, p.Prime → (p ∣ n ↔ p ∣ a * b) := by
  intro p hp
  subst hn
  constructor
  · intro hpn
    rcases hp.dvd_mul.mp hpn with h | h
    · exact Or.elim (hp.dvd_mul.mp (by simpa [sq] using h))
        (fun h => Dvd.dvd.trans h (dvd_mul_right a b))
        (fun h => Dvd.dvd.trans h (dvd_mul_right a b))
    · have : p ∣ b := by
        have h3 : p ∣ b ^ 3 := h
        exact hp.dvd_of_dvd_pow h3
      exact Dvd.dvd.trans this (dvd_mul_left b a)
  · intro hp_ab
    rcases hp.dvd_mul.mp hp_ab with h | h
    · exact dvd_mul_of_dvd_left
        (dvd_pow h (by decide : (2 : ℕ) ≠ 0)) _
    · exact dvd_mul_of_dvd_right
        (dvd_pow h (by decide : (3 : ℕ) ≠ 0)) _

/-- **Chapter bridge corollary.** If `d > 0` is squarefree and `n, n + d, n + 2d`
are all powerful, and `n = a^2 * b^3` is the Golomb decomposition with `Squarefree b`,
then `Nat.Coprime (a * b) d`. -/
theorem powerful_3AP_squarefree_d_coprime_param
    (n d a b : ℕ) (hd : 0 < d) (hsq_d : Squarefree d)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hsq_b : Squarefree b)
    (hn_eq : n = a ^ 2 * b ^ 3)
    (h0 : Powerful n) (h1 : Powerful (n + d)) (h2 : Powerful (n + 2 * d)) :
    Nat.Coprime (a * b) d := by
  have hcop_nd : Nat.Coprime n d :=
    powerful_3AP_squarefree_d_coprime n d hd hsq_d h0 h1 h2
  rw [Nat.coprime_iff_gcd_eq_one] at *
  by_contra hne
  have hg : 0 < Nat.gcd (a * b) d := by
    have hab_pos : 0 < a * b := Nat.mul_pos ha hb
    exact Nat.gcd_pos_of_pos_left d hab_pos
  have hg1 : 1 < Nat.gcd (a * b) d := by omega
  obtain ⟨p, hp_prime, hp_g⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hg1).symm
  have hp_ab : p ∣ a * b := dvd_trans hp_g (Nat.gcd_dvd_left _ _)
  have hp_d : p ∣ d := dvd_trans hp_g (Nat.gcd_dvd_right _ _)
  -- p ∣ a*b ⇒ p ∣ n via the radical bridge.
  have hp_n : p ∣ n := (powerful_radical_eq_radical_param ha hb hsq_b hn_eq p hp_prime).mpr hp_ab
  -- Now gcd(n, d) ≥ p > 1, contradicting Coprime n d.
  have : p ∣ Nat.gcd n d := Nat.dvd_gcd hp_n hp_d
  rw [hcop_nd] at this
  exact hp_prime.one_lt.ne' (Nat.eq_one_of_dvd_one this)

end Nat
