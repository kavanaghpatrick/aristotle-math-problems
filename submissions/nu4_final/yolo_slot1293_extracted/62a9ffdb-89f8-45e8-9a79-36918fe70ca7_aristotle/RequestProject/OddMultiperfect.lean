import Mathlib

open Finset Nat

/-!
# Odd multiperfect impossibility for σ₀(n) ∈ {11, 13, 17, 19}

For every odd n > 1 with σ₀(n) ∈ {11, 13, 17, 19}, n is not multiperfect.

## Proof outline

1. Since σ₀(n) = q is prime and n > 1, n must be p^(q-1) for some prime p.
2. σ(p^(q-1)) = 1 + p + ... + p^(q-1) ≡ 1 (mod p).
3. Multiperfect means σ(n) = k·n, so p | σ(n), contradicting step 2.
-/

/-
If n > 1 and (Nat.divisors n).card = q with q prime, then n = p^(q-1) for some prime p.
-/
lemma card_divisors_prime_implies_prime_pow {n q : ℕ} (hn : n > 1)
    (hq : Nat.Prime q) (hcard : (Nat.divisors n).card = q) :
    ∃ p, Nat.Prime p ∧ n = p ^ (q - 1) := by
  -- By Nat.card (�_div�isors (n ≠ 0 since n > 1), we have (Nat.divisors n).card = ∏ x ∈ n.primeFactors, (n.factorization x + 1). This product equals q, which is prime.
  have h_prod : ∏ x ∈ n.primeFactors, (n.factorization x + 1) = q := by
    rw [ ← hcard, Nat.card_divisors ];
    positivity;
  -- Each factor (n.factorization x + 1) is ≥ 2 since x ∈ primeFactors means factorization x ≥ 1.
  have h_factors_ge_two : ∀ x ∈ n.primeFactors, 2 ≤ n.factorization x + 1 := by
    exact fun x hx => Nat.succ_le_succ ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hx ) );
  -- A product of integers each ≥ 2 that equals a prime must have exactly one factor. So primeFactors has exactly one element p, and n.factorization p + 1 = q.
  have h_prime_factors_one_element : n.primeFactors.card = 1 := by
    have h_prime_factors_one_element : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ x ∈ S, 2 ≤ f x) → (∏ x ∈ S, f x) = q → S.card = 1 := by
      intros S f hf hprod; induction S using Finset.induction <;> simp_all +decide ;
      · exact hq.ne_one hprod.symm;
      · have := hq.isUnit_or_isUnit hprod.symm; aesop;
    exact h_prime_factors_one_element h_factors_ge_two h_prod
  obtain ⟨p, hp⟩ : ∃ p, n.primeFactors = {p} := by
    exact Finset.card_eq_one.mp h_prime_factors_one_element
  have h_factorization_p : n.factorization p + 1 = q := by
    aesop
  have h_n_eq_p_pow : n = p ^ (q - 1) := by
    conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self hn.ne_bot ];
    simp +decide [ ← h_factorization_p, hp, Finsupp.prod ]
  use p, by
    grind, h_n_eq_p_pow

/-
Sum of divisors of p^e equals the geometric sum ∑ i ∈ range (e+1), p^i.
-/
lemma sum_divisors_prime_pow {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    (Nat.divisors (p ^ e)).sum id = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  norm_num [ Nat.divisors_prime_pow hp ]

/-
The geometric sum 1 + p + ... + p^e is ≡ 1 (mod p) for p ≥ 2 and any e.
-/
lemma geom_sum_mod_prime {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) % p = 1 := by
  norm_num [ Finset.sum_nat_mod, Nat.pow_mod, Nat.mod_eq_of_lt hp.one_lt ];
  simp +decide [ Finset.sum_range_succ' ];
  exact Nat.mod_eq_of_lt hp.two_le

/-
p does not divide the geometric sum 1 + p + ... + p^e for prime p.
-/
lemma prime_not_dvd_geom_sum {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    ¬ (p ∣ ∑ i ∈ Finset.range (e + 1), p ^ i) := by
  haveI := Fact.mk hp ; norm_num [ ← ZMod.natCast_eq_zero_iff, geom_sum_mul ]

/-
If n = p^(q-1), p prime, q ≥ 2, and σ(n) = k*n with k ≥ 2, contradiction.
-/
lemma not_multiperfect_prime_pow {p q : ℕ} (hp : Nat.Prime p) (hq : q ≥ 2) :
    ¬ ∃ k : ℕ, k ≥ 2 ∧ (Nat.divisors (p ^ (q - 1))).sum id = k * p ^ (q - 1) := by
  rcases q with ( _ | _ | q ) <;> simp_all +decide [ Nat.divisors_prime_pow ];
  intro x hx; intro H; have := congr_arg ( · % p ) H; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Finset.sum_nat_mod, Nat.mod_eq_of_lt hp.one_lt ] at this;
  simp_all +decide [ Finset.sum_range_succ' ]

theorem odd_multiperfect_sigma0_family_impossible :
    ∀ q ∈ ({11, 13, 17, 19} : Finset ℕ),
      ¬ ∃ n : ℕ, Odd n ∧ n > 1 ∧
        (Nat.divisors n).card = q ∧
        ∃ k : ℕ, k ≥ 2 ∧ ((Nat.divisors n).sum id) = k * n := by
  intros q hq
  by_contra h
  obtain ⟨n, hn_odd, hn_gt1, hn_card, k, hk2, hk⟩ := h
  have h_prime : Nat.Prime q := by
    fin_cases hq <;> norm_num
  have h_eq : ∃ p, Nat.Prime p ∧ n = p ^ (q - 1) := by
    apply card_divisors_prime_implies_prime_pow hn_gt1 h_prime hn_card
  obtain ⟨p, hp, hn_eq⟩ := h_eq
  rw [hn_eq] at hk
  apply not_multiperfect_prime_pow hp (by
  exact h_prime.two_le) ⟨k, hk2, hk⟩