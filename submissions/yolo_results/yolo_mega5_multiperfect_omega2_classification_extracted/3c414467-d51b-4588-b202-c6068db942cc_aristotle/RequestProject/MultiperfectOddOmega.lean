import Mathlib

/-!
# No odd multiperfect numbers with at most 2 distinct prime factors

We prove that for every odd natural number `n > 1` with at most 2 distinct prime factors,
`n` is not multiperfect: there is no integer `k ≥ 2` with `σ(n) = k · n`.

The proof splits into two cases:
- **ω(n) = 1**: `n` is a prime power, and prime powers are deficient by
  `IsPrimePow.deficient`.
- **ω(n) = 2**: `n = p^a · q^b` with distinct odd primes `p ≥ 3`, `q ≥ 5`.
  By multiplicativity of `σ` and the geometric series bound, we show `σ(n) < 2n`.

## Main result

* `not_multiperfect_of_odd_omega_le_two` — the target theorem.
-/

/-- The geometric series identity over ℕ:
`(∑ k ∈ range (a+1), p^k) * (p-1) + 1 = p^(a+1)` for `p ≥ 2`. -/
lemma geom_sum_nat_identity (p a : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Finset.range (a + 1), p ^ k) * (p - 1) + 1 = p ^ (a + 1) := by
  convert geom_sum_mul_add (p - 1) (a + 1) using 1
  · rw [Nat.sub_add_cancel (by linarith)]
  · grind

/-- Bound: `(∑ k ∈ range (a+1), p^k) * (p-1) < p * p^a` for `p ≥ 2`. -/
lemma geom_sum_mul_pred_lt (p a : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Finset.range (a + 1), p ^ k) * (p - 1) < p * p ^ a := by
  convert Nat.lt_of_succ_le (geom_sum_nat_identity p a hp |> le_of_eq) using 1
  ring

/-- Numerical bound: `p * q ≤ 2 * (p-1) * (q-1)` for `p ≥ 3`, `q ≥ 5`. -/
lemma pq_le_two_mul_pred_pred (p q : ℕ) (hp : 3 ≤ p) (hq : 5 ≤ q) :
    p * q ≤ 2 * (p - 1) * (q - 1) := by
  nlinarith [Nat.sub_add_cancel (by linarith : 1 ≤ p),
             Nat.sub_add_cancel (by linarith : 1 ≤ q)]

/-- For `n > 1` with `ω(n) = 1`, `n` is deficient. -/
lemma deficient_of_omega_one {n : ℕ}
    (hw : (Nat.primeFactors n).card = 1) : Nat.Deficient n :=
  IsPrimePow.deficient (isPrimePow_iff_card_primeFactors_eq_one.mpr hw)

/-
Sum of divisors of a product of coprime prime powers equals the product of the
individual sums of divisors. Stated in terms of `Finset.sum id` over `Nat.divisors`.
-/
lemma sum_divisors_mul_of_coprime (a b : ℕ) (h : Nat.Coprime a b) :
    (Nat.divisors (a * b)).sum id = (Nat.divisors a).sum id * (Nat.divisors b).sum id := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide
  convert ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    (show (ArithmeticFunction.sigma 1).IsMultiplicative from
      ArithmeticFunction.isMultiplicative_sigma) h using 1
  · simp +decide [ArithmeticFunction.sigma_apply]
  · simp +decide [ArithmeticFunction.sigma_apply]

/-
For distinct primes `p ≥ 3, q ≥ 5` and positive exponents, `p^a * q^b` is deficient.
-/
lemma deficient_of_two_odd_prime_powers {p q a b : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.Deficient (p ^ a * q ^ b) := by
  -- Let's denote $S_p = \sum_{k=0}^{a} p^k$ and $S_q = \sum_{k=0}^{b} q^k$.
  set S_p := ∑ k ∈ Finset.range (a + 1), p ^ k
  set S_q := ∑ k ∈ Finset.range (b + 1), q ^ k;
  -- By multiplying these inequalities, we get $S_p \cdot S_q \cdot (p - 1) \cdot (q - 1) < p \cdot q \cdot n$.
  have h_mul : S_p * S_q * (p - 1) * (q - 1) < p * q * (p ^ a * q ^ b) := by
    convert mul_lt_mul'' ( geom_sum_mul_pred_lt p a hp.two_le ) ( geom_sum_mul_pred_lt q b hq.two_le ) ( by positivity ) ( by positivity ) using 1 ; ring;
    ring;
  -- By pq_le_two_mul_pred_pred, we have $p \cdot q \leq 2 \cdot (p - 1) \cdot (q - 1)$.
  have h_pq_le : p * q ≤ 2 * (p - 1) * (q - 1) := by
    nlinarith only [ hp3, hq5, Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hq.pos ];
  -- By combining the inequalities from h_mul and h_pq_le, we get $S_p \cdot S_q < 2 \cdot (p^a \cdot q^b)$.
  have h_combined : S_p * S_q < 2 * (p ^ a * q ^ b) := by
    nlinarith [ show 0 < ( p - 1 ) * ( q - 1 ) by exact mul_pos ( Nat.sub_pos_of_lt hp.one_lt ) ( Nat.sub_pos_of_lt hq.one_lt ), show 0 < p ^ a * q ^ b by positivity ];
  -- By definition of $S_p$ and $S_q$, we have $(Nat.divisors (p ^ a * q ^ b)).sum id = S_p * S_q$.
  have h_sum : (Nat.divisors (p ^ a * q ^ b)).sum id = S_p * S_q := by
    have h_sum : (Nat.divisors (p ^ a * q ^ b)).sum id = (Nat.divisors (p ^ a)).sum id * (Nat.divisors (q ^ b)).sum id := by
      convert sum_divisors_mul_of_coprime ( p ^ a ) ( q ^ b ) ( Nat.coprime_pow_primes a b hp hq hpq ) using 1;
    simp_all +decide [ Nat.divisors_prime_pow ];
    rfl;
  simp_all +decide [ Nat.Deficient ];
  rw [ Nat.sum_divisors_eq_sum_properDivisors_add_self ] at h_sum ; linarith

/-
For odd `n > 1` with `ω(n) = 2`, `n` is deficient.
-/
lemma deficient_of_odd_omega_two {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hw : (Nat.primeFactors n).card = 2) : Nat.Deficient n := by
  -- By Finset.card_eq_two, get p, q with p � ≠� q and n.primeFactors = {p, q}.
  obtain ⟨p, q, hpq, h_prime_factors⟩ : ∃ p q : ℕ, p ≠ q ∧ n.primeFactors = {p, q} := by
    rw [ Finset.card_eq_two ] at hw; tauto;
  -- Since both p and q are odd primes, we can apply the lemma for two odd prime powers.
  have h_odd_pq : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q := by
    simp_all +decide [ Finset.ext_iff ];
    exact ⟨ by simpa using h_prime_factors p |>.2 ( Or.inl rfl ) |>.1, by simpa using h_prime_factors q |>.2 ( Or.inr rfl ) |>.1, Nat.succ_le_of_lt ( lt_of_le_of_ne ( Nat.Prime.two_le ( by simpa using h_prime_factors p |>.2 ( Or.inl rfl ) |>.1 ) ) ( Ne.symm <| by rintro rfl; exact absurd ( hodd.of_dvd_nat <| h_prime_factors _ |>.2 ( Or.inl rfl ) |>.2.1 ) ( by decide ) ) ), Nat.succ_le_of_lt ( lt_of_le_of_ne ( Nat.Prime.two_le ( by simpa using h_prime_factors q |>.2 ( Or.inr rfl ) |>.1 ) ) ( Ne.symm <| by rintro rfl; exact absurd ( hodd.of_dvd_nat <| h_prime_factors _ |>.2 ( Or.inr rfl ) |>.2.1 ) ( by decide ) ) ) ⟩;
  -- Let $a = n.factorization p$ and $b = n.factorization q$. Since $p, q \in primeFactors n$, $a \ge 1$ and $b \ge 1$.
  obtain ⟨a, b, ha, hb⟩ : ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ n = p ^ a * q ^ b := by
    exact ⟨ n.factorization p, n.factorization q, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self hn.ne_bot ] ; rw [ Finsupp.prod ] ; aesop ⟩;
  -- By Nat.factorization_prod_pow_eq_self (since n > 1 so n ≠ 0), n = n.factorization.prod (· ^ ·). Since the support of n.factorization = n.primeFactors = � {�p, q}, this product equals p^a * q^b.
  rw [hb.right];
  by_cases hpq' : p < q;
  · -- Since $p < q$, we have $q \ge 5$.
    have hq_ge_5 : 5 ≤ q := by
      exact le_of_not_gt fun h => by interval_cases q <;> interval_cases p <;> simp_all +decide ;
    exact deficient_of_two_odd_prime_powers h_odd_pq.1 h_odd_pq.2.1 hpq h_odd_pq.2.2.2.1 hq_ge_5 ha hb.1;
  · have h_deficient : Nat.Deficient (q ^ b * p ^ a) := by
      apply deficient_of_two_odd_prime_powers;
      all_goals try linarith;
      · tauto;
      · tauto;
      · grind;
      · exact le_of_not_gt fun h => by have := h_odd_pq.2.1.eq_two_or_odd; have := h_odd_pq.1.eq_two_or_odd; omega;
    rwa [ mul_comm ]

/-- If `n` is deficient, then `n` is not multiperfect. -/
lemma not_multiperfect_of_deficient {n : ℕ}
    (hdef : Nat.Deficient n) :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ (Nat.divisors n).sum id = k * n := by
  contrapose! hdef
  rcases n with (_ | _ | n) <;> simp_all +arith +decide [Nat.Deficient]
  obtain ⟨k, hk₁, hk₂⟩ := hdef
  erw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hk₂
  nlinarith

/-
**Main theorem**: No odd natural number `n > 1` with at most 2 distinct prime factors
is multiperfect.
-/
theorem not_multiperfect_of_odd_omega_le_two {n : ℕ} (hn : 1 < n)
    (hodd : Odd n) (hw : (Nat.primeFactors n).card ≤ 2) :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ (Nat.divisors n).sum id = k * n := by
  by_cases h1 : ( Nat.primeFactors n ).card = 1;
  · exact not_multiperfect_of_deficient ( deficient_of_omega_one h1 );
  · convert not_multiperfect_of_deficient ( deficient_of_odd_omega_two hn hodd _ ) using 1;
    exact le_antisymm hw ( Nat.lt_of_le_of_ne ( Nat.pos_of_ne_zero ( by aesop ) ) ( Ne.symm h1 ) )