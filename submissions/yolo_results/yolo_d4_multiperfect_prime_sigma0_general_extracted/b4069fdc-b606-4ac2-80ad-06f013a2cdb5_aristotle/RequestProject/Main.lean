import Mathlib

/-
If n > 1 and σ₀(n) is prime, then n is a prime power.
-/
lemma isPrimePow_of_prime_card_divisors {n : ℕ} (hn : 1 < n)
    (hp : Nat.Prime (Nat.divisors n).card) : IsPrimePow n := by
  -- Use Nat.card_divisors to rewrite the card as ∏ p ∈ n.primeFactors, (n.factorization p + 1).
  have h_card : n.divisors.card = ∏ p ∈ n.primeFactors, (Nat.factorization n p + 1) := by
    exact Nat.card_divisors hn.ne_bot;
  -- Each factor in the product is ≥ 2, so the product is prime only if there is exactly one prime factor.
  have h_prime_factors : n.primeFactors.card = 1 := by
    induction h : n.primeFactors using Finset.induction <;> simp_all +decide [ Nat.prime_mul_iff ];
    simp_all +decide [ Nat.factorization_eq_zero_iff, Finset.ext_iff ];
    grind;
  grind +suggestions

/-
No multiperfect number n > 1 can have a prime number of divisors.
-/
theorem not_multiperfect_of_prime_card_divisors {n : ℕ} (hn : 1 < n)
    (hp : Nat.Prime (Nat.divisors n).card) :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ (Nat.divisors n).sum id = k * n := by
  -- By assumption, n is a prime power, so n is deficient.
  have h_deficient : Nat.Deficient n := by
    apply IsPrimePow.deficient;
    -- Apply the lemma that states if n > 1 and the number of divisors is prime, then n is a prime power.
    apply isPrimePow_of_prime_card_divisors hn hp;
  simp_all +decide [ Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.Deficient ];
  exact fun x hx => by nlinarith;