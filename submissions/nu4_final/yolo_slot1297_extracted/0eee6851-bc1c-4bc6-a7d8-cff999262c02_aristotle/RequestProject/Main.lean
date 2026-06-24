import Mathlib

set_option maxHeartbeats 8000000

/-!
# Uniform odd-multiperfect impossibility for σ₀(n) ∈ {11, 13, 17, 19}

## Proof outline

The key insight is elementary number theory, not algebraic geometry:

1. If σ₀(n) is prime q, then n must be a prime power p^(q-1), since
   σ₀(n) = ∏ (aᵢ+1) and this product being prime forces exactly one factor.
2. Prime powers are deficient (σ(n) < 2n), by `IsPrimePow.deficient`.
3. Therefore σ(n) = k·n with k ≥ 2 is impossible since it would require σ(n) ≥ 2n.
-/

/-
A product over a finset where each factor ≥ 2 that equals a prime
must come from a singleton finset. In other words, if ∏ f(x) is prime
and each f(x) ≥ 2, the finset has exactly one element.
-/
lemma Finset.prod_prime_of_ge_two {s : Finset ℕ} {f : ℕ → ℕ}
    (hprime : Nat.Prime (∏ x ∈ s, f x))
    (hge : ∀ x ∈ s, f x ≥ 2) :
    ∃ a ∈ s, f a = ∏ x ∈ s, f x ∧ ∀ b ∈ s, b ≠ a → f b = 1 := by
  -- Since the product is prime, there must be exactly one element in s.
  obtain ⟨a, ha⟩ : ∃ a ∈ s, (∏ x ∈ s \ {a}, (f x)) = 1 := by
    by_cases hs : s.Nonempty <;> simp_all +decide;
    obtain ⟨ a, ha ⟩ := hs; use a, ha; contrapose! hprime; simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton ha, Nat.prime_mul_iff ] ;
    exact fun _ => ne_of_gt ( hge a ha );
  simp_all +decide [ Finset.prod_eq_prod_diff_singleton_mul ha.1 ];
  exact ⟨ a, ha.1, by rw [ Finset.prod_eq_one fun x hx => ha.2 x ( Finset.mem_sdiff.mp hx |>.1 ) ( by aesop ) ] ; ring, ha.2 ⟩

/-
If n > 1 and σ₀(n) is prime, then n is a prime power.
-/
lemma isPrimePow_of_prime_card_divisors {n : ℕ} (hn : n > 1)
    (hp : Nat.Prime (n.divisors.card)) : IsPrimePow n := by
  -- Since σ₀(n) is prime, the factorization ∏(aᵢ+1) forces exactly one prime factor.
  have h_prime_factors : (Nat.primeFactors n).card = 1 := by
    -- By Nat.card_divisors, n.divisors.card = ∏ x ∈ n.primeFactors, (n.factorization x + 1).
    have h_card_divisors : n.divisors.card = ∏ x ∈ n.primeFactors, (Nat.factorization n x + 1) := by
      convert Nat.card_divisors hn.ne_bot;
    simp_all +decide [ Nat.prime_iff ];
    have h_prime_factors : ∀ {s : Finset ℕ} {f : ℕ → ℕ}, (∀ x ∈ s, f x ≥ 2) → Nat.Prime (∏ x ∈ s, f x) → s.card = 1 := by
      intros s f hf hprime; induction s using Finset.induction <;> simp_all +decide [ Nat.prime_mul_iff ] ;
      grind;
    exact h_prime_factors ( fun x hx => Nat.succ_le_succ ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hx ) ) ) ( by simpa only [ ← Nat.prime_iff ] using hp );
  grind +suggestions

/-
If n is deficient and n > 0, then σ(n) < 2*n, so n cannot be multiperfect.
-/
lemma not_multiperfect_of_deficient {n : ℕ} (_hn : n > 0)
    (hdef : n.Deficient) :
    ¬ ∃ k : ℕ, k ≥ 2 ∧ (n.divisors.sum id) = k * n := by
  simp [Nat.Deficient] at *;
  intro k hk; rw [ Nat.sum_divisors_eq_sum_properDivisors_add_self ] ; nlinarith;

theorem odd_multiperfect_sigma0_family_impossible :
    ∀ q ∈ ({11, 13, 17, 19} : Finset ℕ),
      ¬ ∃ n : ℕ, Odd n ∧ n > 1 ∧
        (Nat.divisors n).card = q ∧
        ∃ k : ℕ, k ≥ 2 ∧ ((Nat.divisors n).sum id) = k * n := by
  -- For each q, show it's prime, deduce IsPrimePow, then Deficient, then contradiction.
  intro q hq
  by_contra h
  obtain ⟨n, hn_odd, hn_gt1, hn_card, k, hk_ge2, hk_eq⟩ := h
  have h_deficient : n.Deficient := by
    convert IsPrimePow.deficient _;
    convert isPrimePow_of_prime_card_divisors hn_gt1 _ ; aesop ( simp_config := { decide := true } ) ;
  have h_not_multiperfect : ¬∃ k : ℕ, k ≥ 2 ∧ (n.divisors.sum id) = k * n := by
    apply not_multiperfect_of_deficient; exact Nat.zero_lt_of_lt hn_gt1; exact h_deficient;
  exact h_not_multiperfect ⟨k, hk_ge2, hk_eq⟩