import Mathlib

open Finset Nat BigOperators

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-
If n > 1 and σ₀(n) is prime, then n is a prime power p^(q-1).
-/
lemma isPrimePow_of_card_divisors_prime {n : ℕ} (hn : n > 1)
    (hq : Nat.Prime (n.divisors.card)) :
    ∃ p : ℕ, Nat.Prime p ∧ n = p ^ (n.divisors.card - 1) := by
  rw [ Nat.card_divisors hn.ne_bot ] at hq;
  -- Since each factor (n.factorization x + 1) ≥ 2 (as x ∈ primeFactors means factorization x ≥ 1), and the product is prime, there's exactly one prime factor p.
  obtain ⟨p, hp⟩ : ∃ p, p ∈ n.primeFactors ∧ ∀ q ∈ n.primeFactors, q = p := by
    rcases k : n.primeFactors with ( _ | ⟨ p, hp ⟩ ) ; simp_all +decide [ Nat.prime_mul_iff ];
    rcases x : ( ‹_› : List ℕ ) with ( _ | ⟨ p, _ | ⟨ q, l ⟩ ⟩ ) <;> simp_all +decide [ Nat.prime_mul_iff ];
    replace k := Finset.ext_iff.mp k; have := k p; have := k q; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
    grind +ring;
  -- Then n = p^(factorization p) and factorization p + 1 = q, so factorization p = q - 1.
  have h_factorization : n = p^(n.factorization p) ∧ n.factorization p + 1 = #n.divisors := by
    rw [ ← Nat.factorization_prod_pow_eq_self hn.ne_bot ];
    simp_all +decide [ Finsupp.prod ];
    rw [ Finset.prod_eq_single p ] <;> simp_all +decide [ Nat.factorization_eq_zero_iff ];
    rw [ Nat.divisors_prime_pow hp.1.1, Finset.card_map, Finset.card_range ];
  grind

/-
The sum of divisors of p^e equals the geometric sum 1 + p + ... + p^e.
-/
lemma sum_divisors_prime_pow (p : ℕ) (hp : Nat.Prime p) (e : ℕ) :
    ((p ^ e).divisors.sum id) = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  simp +decide [ Nat.divisors_prime_pow hp, Finset.sum_range_succ' ]

/-
For p ≥ 3 and e ≥ 1, the geometric sum 1 + p + ... + p^e is strictly less than 2 * p^e.
-/
lemma geom_sum_lt_two_mul {p e : ℕ} (hp : p ≥ 3) (he : e ≥ 1) :
    ∑ i ∈ Finset.range (e + 1), p ^ i < 2 * p ^ e := by
  induction he <;> simp_all +decide [ Finset.sum_range_succ ] ; nlinarith [ pow_succ p ‹_› ];
  norm_num [ pow_succ' ] at * ; nlinarith [ pow_pos ( by linarith : 0 < p ) ‹_› ]

/-
An odd prime power p^e with e ≥ 1 has sum of divisors < 2 * p^e.
-/
lemma sigma_lt_two_mul_of_odd_prime_pow {p e : ℕ} (hp : Nat.Prime p) (hodd : Odd (p ^ e))
    (he : e ≥ 1) :
    (Nat.divisors (p ^ e)).sum id < 2 * p ^ e := by
  -- Since p is an odd prime, we have p ≥ 3.
  have hp_ge_three : p ≥ 3 := by
    contrapose! hodd; interval_cases p <;> simp_all +decide ;
    exact even_iff_two_dvd.mpr ( dvd_pow_self _ ( by linarith ) );
  rw [ sum_divisors_prime_pow p hp e ];
  exact geom_sum_lt_two_mul hp_ge_three he

/-
Main theorem: for q ∈ {11, 13, 17, 19}, no odd n > 1 with σ₀(n) = q is multiperfect.
-/
theorem odd_multiperfect_sigma0_family_impossible :
    ∀ q ∈ ({11, 13, 17, 19} : Finset ℕ),
      ¬ ∃ n : ℕ, Odd n ∧ n > 1 ∧
        (Nat.divisors n).card = q ∧
        ∃ k : ℕ, k ≥ 2 ∧ ((Nat.divisors n).sum id) = k * n := by
  -- For each q ∈ {11,13,17,19}, use `Finset.forall_mem` / `simp` to dispatch.
  intro q hq
  by_contra h
  obtain ⟨n, hodd, hn1, hcard, k, hk2, hσ⟩ := h
  have h_prime : Nat.Prime q := by
    fin_cases hq <;> norm_num;
  -- Use `isPrimePow_of_card_div �isors�_prime` to get p prime with n = p^(q-1).
  obtain ⟨p, hp_prime, hn_eq⟩ : ∃ p : ℕ, Nat.Prime p ∧ n = p ^ (q - 1) := by
    grind +suggestions;
  -- Since n is odd, p^(q-1) is odd, so by sigma_lt_two_mul_of_odd_prime_pow, σ(p^(q-1)) < � �2*p^(q-1).
  have h_sigma_lt_two_mul : (Nat.divisors (p ^ (q - 1))).sum id < 2 * p ^ (q - 1) := by
    apply sigma_lt_two_mul_of_odd_prime_pow hp_prime;
    · grind;
    · exact Nat.sub_pos_of_lt h_prime.one_lt;
  simp_all +decide [ mul_comm ] ; nlinarith;