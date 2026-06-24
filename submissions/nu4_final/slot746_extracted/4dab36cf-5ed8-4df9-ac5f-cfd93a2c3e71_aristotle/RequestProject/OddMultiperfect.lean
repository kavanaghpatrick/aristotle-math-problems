import Mathlib

open Finset Nat

/-!
# No odd multiperfect number has exactly 11 divisors

Since 11 is prime, any natural number n with σ₀(n) = 11 must be of the form p^10
for some prime p. If n is also odd, then p is an odd prime.

σ(p^10) = 1 + p + p^2 + … + p^10 ≡ 1 (mod p), so p ∤ σ(p^10).
But if σ(p^10) = k · p^10 for k ≥ 2, then p^10 ∣ σ(p^10), hence p ∣ σ(p^10),
contradicting p ∤ σ(p^10).
-/

/-
Helper: if n has exactly 11 divisors, then n = p^10 for some prime p
-/
lemma card_divisors_eq_prime_of_eleven {n : ℕ} (hn : n > 1)
    (hd : (Nat.divisors n).card = 11) :
    ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 10 := by
      -- Use Nat.card_divisors to write ( �Nat�.divisors n).card as x in n �.pr�imeFactors, (n.factorization x + 1). Since this product equals 11 and 11 is prime, the product has exactly one factor, so n has exactly one prime factor p, and n.factorization p + 1 = 11, so n.factorization p = 10, hence n = p^10.
      have h_prime_factors : n.primeFactors.card = 1 := by
        -- Since the product of � (�n.factorization x + 1) over all prime factors x of n equals 11, and 11 is prime,
        -- each factor (n.factorization x + 1) must be 1 or 11. However, since each term is at least 2, it must be 11.
        have h_factors : ∀ x ∈ n.primeFactors, n.factorization x + 1 = 11 := by
          -- Since $\sigma(n)$ is prime � and� equals 11, it must be that each $(n.factorization x + 1)$ is a factor of 11.
          have h_factor : ∀ x ∈ n.primeFactors, (n.factorization x + 1) ∣ 11 := by
            rw [ ← hd, @Nat.card_divisors ];
            · exact fun x hx => Finset.dvd_prod_of_mem _ hx;
            · positivity;
          intro x hx; specialize h_factor x hx; have := Nat.le_of_dvd ( by decide ) h_factor; interval_cases _ : n.factorization x + 1 <;> simp_all +decide ;
          simp_all +decide [ Nat.factorization_eq_zero_iff ];
        have := @Nat.card_divisors n hn.ne_bot; simp_all +decide [ ] ;
        exact Nat.pow_right_injective ( by decide ) hd;
      -- Since n has exactly one prime � factor� p, we can write n as p^k for some integer k.
      obtain ⟨p, k, hp, rfl⟩ : ∃ p k : ℕ, Nat.Prime p ∧ n = p^k := by
        rw [ Finset.card_eq_one ] at h_prime_factors;
        exact ⟨ h_prime_factors.choose, n.factorization h_prime_factors.choose, Nat.prime_of_mem_primeFactors <| h_prime_factors.choose_spec.symm ▸ Finset.mem_singleton_self _, by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self hn.ne_bot ] ; rw [ Finsupp.prod ] ; aesop ⟩;
      simp_all +decide [ Nat.divisors_prime_pow ]

/-
Helper: σ(p^10) mod p = 1 for any prime p
-/
lemma sigma_prime_pow_mod (p : ℕ) (hp : Nat.Prime p) :
    (Nat.divisors (p ^ 10)).sum id % p = 1 := by
      norm_num [ Nat.divisors_prime_pow hp, Finset.sum_range_succ' ];
      norm_num [ Nat.add_mod, Nat.pow_mod, Nat.mod_eq_of_lt hp.one_lt ]

/-
Helper: if p^10 divides m then p divides m
-/
lemma prime_dvd_of_pow_dvd {p m : ℕ} (_hp : Nat.Prime p) (h : p ^ 10 ∣ m) :
    p ∣ m :=
  dvd_trans (dvd_pow_self _ (by decide)) h

/-
Main theorem
-/
theorem odd_multiperfect_sigma0_11_impossible :
    ¬ ∃ n : ℕ, Odd n ∧ n > 1 ∧
      (Nat.divisors n).card = 11 ∧
      ∃ k : ℕ, k ≥ 2 ∧ ((Nat.divisors n).sum id) = k * n := by
        intro h
        obtain ⟨n, h_odd, h_gt1, h_card, k, hk_ge2, h_sigma⟩ := h

        -- From card_divisors_eq_prime_of_eleven, n = p^10 for some prime p.
        obtain ⟨p, hp_prime, hn⟩ : ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 10 := by
          -- Apply the lemma that states if a number has exactly 11 divisors, it must be of the form p^10 for some prime p.
          apply card_divisors_eq_prime_of_eleven h_gt1 h_card;
        simp_all +decide [ Nat.divisors_prime_pow ];
        norm_num [ Finset.sum_range_succ ] at h_sigma ; nlinarith [ pow_pos hp_prime.pos 2, pow_pos hp_prime.pos 3, pow_pos hp_prime.pos 4, pow_pos hp_prime.pos 5, pow_pos hp_prime.pos 6, pow_pos hp_prime.pos 7, pow_pos hp_prime.pos 8, pow_pos hp_prime.pos 9, pow_pos hp_prime.pos 10 ] ;