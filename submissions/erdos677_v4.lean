/-
Erdős Problem #677 - LCM of Consecutive Integers
VERSION 4: Binomial Coefficient Approach for Sylvester-Schur

=== STRATEGY (from Grok-4 analysis) ===
The standard elementary proof of Sylvester-Schur uses binomial coefficients:

1. C(n+k, k) = (n+1)(n+2)...(n+k) / k! is an INTEGER
2. Assume all factors (n+1),...,(n+k) are k-smooth (prime factors ≤ k)
3. For each prime p ≤ k, compare p-adic valuations:
   - v_p(numerator) = sum of v_p(n+i) for i in [1,k]
   - v_p(k!) = Legendre's formula
4. For n ≥ k, the binomial is too large → contradiction

This avoids heavy prime counting machinery!

=== MATHLIB TOOLS ===
- Nat.bertrand: For n ≥ 1, ∃ prime p with n < p ≤ 2n
- padicValNat: p-adic valuation in Mathlib
- Nat.choose_pos: C(n+k,k) > 0
- Nat.factorial_dvd_factorial: divisibility of factorials

=== YOUR PROVEN LEMMAS (from v3) ===
All 10 lemmas from v3 included with full proofs.

=== NEW TARGETS ===
1. k_smooth_product_bound: If all factors k-smooth, bound the product
2. sylvester_schur: Via binomial contradiction
3. erdos_677: Main theorem
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Nat

/-- M(n,k) = lcm of k consecutive integers starting from n+1 -/
def M (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-! ## YOUR PROVEN LEMMAS (from v3) -/

/-- Product of k consecutive integers ≥ k! [PROVEN] -/
lemma product_consecutive_ge_factorial (n k : ℕ) (hk : k ≥ 1) :
    (Finset.Ioc n (n + k)).prod id ≥ k.factorial := by
  have h_prod_ge_factorial : ∀ m : ℕ, (∏ i ∈ Finset.range k, (m + i + 1)) ≥ k ! := by
    intro m; induction hk <;> simp_all +decide [Nat.factorial_succ, Finset.prod_range_succ]; nlinarith
  convert h_prod_ge_factorial n |> le_trans <| le_of_eq _ using 1
  refine' Finset.prod_bij (fun x hx => n + x + 1) _ _ _ _ <;> aesop
  · grind
  · grind +ring
  · exact ⟨b - n - 1, by omega, by omega⟩

/-- If p > k, at most one multiple of p in any k-length interval [PROVEN] -/
lemma unique_multiple_of_large_prime (x k p : ℕ) (hp : p > k) :
    ∀ y₁ ∈ Finset.Ioc x (x + k), ∀ y₂ ∈ Finset.Ioc x (x + k),
    p ∣ y₁ → p ∣ y₂ → y₁ = y₂ := by
  intro y₁ hy₁ y₂ hy₂ hdiv₁ hdiv₂
  simp only [mem_Ioc] at hy₁ hy₂
  obtain ⟨a, rfl⟩ := hdiv₁
  obtain ⟨b, rfl⟩ := hdiv₂
  by_contra hab
  have : a ≠ b := by intro h; exact hab (by rw [h])
  have hne : (a : ℤ) ≠ b := by exact_mod_cast this
  have hdiff : |((a : ℤ) - b)| ≥ 1 := Int.one_le_abs (sub_ne_zero.mpr hne)
  have hbound : |((a : ℤ) - b) * p| < k := by
    have h1 : (a : ℤ) * p ≤ x + k := by exact_mod_cast hy₁.2
    have h2 : (b : ℤ) * p ≤ x + k := by exact_mod_cast hy₂.2
    have h3 : (a : ℤ) * p > x := by exact_mod_cast hy₁.1
    have h4 : (b : ℤ) * p > x := by exact_mod_cast hy₂.1
    have : |((a : ℤ) * p - b * p)| < k := by nlinarith
    simp only [← sub_mul] at this
    exact this
  have : |((a : ℤ) - b)| * p < k := by
    rw [abs_mul] at hbound
    simp only [abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (show p ≠ 0 by omega) : (0 : ℤ) < p)] at hbound
    exact hbound
  have : (1 : ℤ) * p < k := by nlinarith
  simp at this
  omega

/-- If p | j and j ∈ (n, n+k], then p | M(n,k) [PROVEN] -/
lemma prime_divides_M_via_elem (n k j p : ℕ) (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hdiv : p ∣ j) : p ∣ M n k := by
  unfold M
  apply dvd_trans hdiv
  exact Finset.dvd_lcm hj

/-- m+k divides M(m,k) [PROVEN] -/
lemma mk_divides_M (m k : ℕ) (hk : k ≥ 1) : m + k ∣ M m k := by
  unfold M
  exact Finset.dvd_lcm (by simp [Finset.mem_Ioc]; omega)

/-- M is positive [PROVEN] -/
lemma M_pos (n k : ℕ) (hk : k ≥ 1) : M n k > 0 := by
  unfold M
  apply Finset.lcm_pos
  simp [Finset.Ioc_eq_empty_iff]
  omega

/-- FORBIDDEN ZONE - KEY STRUCTURAL THEOREM [PROVEN] -/
theorem forbidden_zone (n k j m p : ℕ) (hk : k ≥ 1)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hpk : p > k) (hpdiv : p ∣ j)
    (hm_lo : m ≥ n + k) (hm_hi : m + k < j + p) :
    M n k ≠ M m k := by
  intro heq
  have hdiv_n : p ∣ M n k := prime_divides_M_via_elem n k j p hj hp hpdiv
  rw [heq] at hdiv_n
  have hprime_dvd : ∃ y ∈ Finset.Ioc m (m + k), p ∣ y := by
    unfold M at hdiv_n
    by_contra h
    push_neg at h
    have hcop : ∀ x ∈ Finset.Ioc m (m + k), Nat.Coprime p x := by
      intro x hx
      exact hp.coprime_iff_not_dvd.mpr (h x hx)
    have : Nat.Coprime p ((Finset.Ioc m (m + k)).lcm id) := by
      apply Nat.Coprime.symm
      apply Finset.coprime_lcm
      intro x hx
      exact (hcop x hx).symm
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdiv_n (dvd_refl p) this.symm
  obtain ⟨y, hy_mem, hy_div⟩ := hprime_dvd
  simp only [mem_Ioc] at hy_mem hj
  obtain ⟨a, rfl⟩ := hpdiv
  obtain ⟨b, rfl⟩ := hy_div
  have hb_gt_a : b > a := by
    have h1 : b * p > m := hy_mem.1
    have h2 : m ≥ a * p := by
      have : a * p ≤ n + k := hj.2
      omega
    nlinarith
  have : b * p ≥ (a + 1) * p := by nlinarith
  have : b * p ≥ a * p + p := by ring_nf; ring_nf at this; exact this
  omega

/-- Forbidden zone range corollary [PROVEN] -/
lemma forbidden_zone_range (n k j p : ℕ) (hk : k ≥ 1)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hpk : p > k) (hpdiv : p ∣ j) :
    ∀ m, n + k ≤ m → m + k < j + p → M n k ≠ M m k := by
  intro m hm_lo hm_hi
  exact forbidden_zone n k j m p hk hj hp hpk hpdiv hm_lo hm_hi

/-- Next zone contains new multiple [PROVEN] -/
lemma next_zone_contains_new_multiple (n k j m p : ℕ)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hm : m ≥ j + p - k) :
    j + p ∈ Finset.Ioc m (m + k) := by
  simp only [mem_Ioc] at hj ⊢
  omega

/-- For large m, M grows [PROVEN] -/
lemma M_grows_large (n k m : ℕ) (hk : k ≥ 1) (hm : m + k > M n k) :
    M m k ≠ M n k := by
  intro heq
  have hdiv : m + k ∣ M m k := mk_divides_M m k hk
  rw [heq] at hdiv
  have hMpos : M n k > 0 := M_pos n k hk
  have : m + k ≤ M n k := Nat.le_of_dvd hMpos hdiv
  omega

/-- M upper bound [PROVEN] -/
lemma M_upper_bound (n k : ℕ) (hk : k ≥ 1) :
    M n k ≤ (Finset.Ioc n (n + k)).prod id := by
  unfold M
  exact Finset.lcm_le_prod id (by simp) (by intro i hi; simp [mem_Ioc] at hi; omega)

/-! ## NEW: BINOMIAL COEFFICIENT APPROACH -/

/-- The binomial coefficient C(n+k, k) = prod / k! -/
lemma binomial_eq_prod_div_factorial (n k : ℕ) :
    Nat.choose (n + k) k * k.factorial = (Finset.Ioc n (n + k)).prod id := by
  -- C(n+k, k) * k! = (n+k)! / n! = (n+1)(n+2)...(n+k)
  rw [Nat.choose_symm_diff]
  simp only [add_sub_cancel_left]
  rw [Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ n + k)]
  -- (n+k)! / n! = prod of (n+1) to (n+k)
  have : (n + k).factorial = n.factorial * (Finset.Ioc n (n + k)).prod id := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.Ioc_succ_right, Finset.prod_insert (by simp [mem_Ioc]; omega)]
      · rw [mul_comm ((Finset.Ioc n (n + k)).prod id), ← mul_assoc]
        conv_lhs => rw [add_succ, Nat.factorial_succ]
        rw [ih]
        ring
      · simp [mem_Ioc]; omega
  omega

/-- Key: C(n+k,k) ≥ 2^k for n ≥ k (binomial growth) -/
lemma binomial_lower_bound (n k : ℕ) (hn : n ≥ k) :
    Nat.choose (n + k) k ≥ 2^k := by
  -- Each factor (n+i)/i ≥ 2 when n ≥ k and i ≤ k
  -- So the product ≥ 2^k
  sorry

/-- A number is k-smooth if all its prime factors are ≤ k -/
def IsKSmooth (k m : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ m → p ≤ k

/-- Product of k-smooth numbers is k-smooth -/
lemma prod_k_smooth (k : ℕ) (s : Finset ℕ) (h : ∀ x ∈ s, IsKSmooth k x) :
    IsKSmooth k (s.prod id) := by
  sorry

/-- KEY LEMMA: If all elements in [n+1, n+k] are k-smooth, bound the product

    The p-adic valuation of the product is bounded by the number of
    multiples of p, p², p³, ... in the interval.

    For an interval of length k, there are at most k/p multiples of p,
    k/p² multiples of p², etc.

    Total: v_p(prod) ≤ k/p + k/p² + k/p³ + ... = k/(p-1) < k for p ≥ 2

    So v_p(prod) < k for all primes p.
    But k! has v_p(k!) = k/p + k/p² + ... by Legendre.

    For C(n+k,k) = prod/k! to be an integer, we need v_p(prod) ≥ v_p(k!).
    This is satisfied, but the KEY is that the product can't be TOO large
    if it's only k-smooth.
-/
lemma k_smooth_product_bound (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k)
    (h_smooth : ∀ j ∈ Finset.Ioc n (n + k), IsKSmooth k j) :
    (Finset.Ioc n (n + k)).prod id < (k.factorial) ^ 2 := by
  -- If all factors are k-smooth, the product is bounded
  -- This contradicts product_consecutive_ge_factorial for large n
  sorry

/-! ## KEY TARGET: Sylvester-Schur via Binomial Contradiction -/

/-- SYLVESTER-SCHUR: For n ≥ k ≥ 1, some element in [n+1, n+k] has a prime factor > k.

    PROOF STRATEGY (binomial approach):
    1. Suppose all elements in [n+1, n+k] are k-smooth (for contradiction)
    2. Then the product (n+1)...(n+k) is k-smooth
    3. By k_smooth_product_bound, product < (k!)²
    4. But by product_consecutive_ge_factorial, product ≥ k!
    5. And for n ≥ k, product ≥ (k+1)(k+2)...(2k) ≥ k! * 2^k / k = 2^k * (k-1)!
    6. For k ≥ some small constant, this exceeds (k!)², contradiction

    ALTERNATIVE: Use Nat.bertrand (Bertrand's postulate in Mathlib)
    For k+1 ≥ 2, there's a prime p with k+1 < p ≤ 2(k+1)
    If n ≥ k, then n+k ≥ 2k, and we can find p in our interval...
-/
theorem sylvester_schur (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j := by
  -- Approach 1: Contrapositive with k-smooth bound
  by_contra h_all_smooth
  push_neg at h_all_smooth
  -- All elements are k-smooth
  have h_smooth : ∀ j ∈ Finset.Ioc n (n + k), IsKSmooth k j := by
    intro j hj
    intro p hp hdiv
    by_contra hpk
    push_neg at hpk
    exact h_all_smooth j hj p hp hpk hdiv
  -- Get contradiction from bounds
  have h_prod_ge := product_consecutive_ge_factorial n k hk
  have h_prod_lt := k_smooth_product_bound n k hk hn h_smooth
  -- For n ≥ k, the product is large: each factor ≥ k+1, so prod ≥ (k+1)^k
  have h_large : (Finset.Ioc n (n + k)).prod id ≥ (k + 1) ^ k := by
    apply Finset.prod_le_pow_card
    intro x hx
    simp [mem_Ioc] at hx
    omega
  -- (k+1)^k > (k!)² for k ≥ 3 or so
  sorry

/-! ## MAIN THEOREM -/

/-- Erdős #677 for n ≥ k -/
theorem erdos_677_n_ge_k (n k m : ℕ) (hk : k ≥ 1) (hn : n ≥ k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  obtain ⟨j, hj, p, hp, hpk, hpdiv⟩ := sylvester_schur n k hk hn
  by_cases hzone : m + k < j + p
  · exact forbidden_zone n k j m p hk hj hp hpk hpdiv hm hzone
  · push_neg at hzone
    by_cases hlarge : m + k > M n k
    · exact (M_grows_large n k m hk hlarge).symm
    · push_neg at hlarge
      have h_contains : j + p ∈ Finset.Ioc m (m + k) := by
        simp only [mem_Ioc] at hj ⊢
        omega
      have hp_div_m : p ∣ M m k := prime_divides_M_via_elem m k (j + p) p h_contains hp (by
        exact dvd_add hpdiv (dvd_refl p))
      sorry

/-- Erdős #677 for n < k -/
theorem erdos_677_n_lt_k (n k m : ℕ) (hk : k ≥ 1) (hn : n < k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  have hm_ge_k : m ≥ k := by omega
  obtain ⟨j, hj, p, hp, hpk, hpdiv⟩ := sylvester_schur m k hk hm_ge_k
  sorry

/-- ERDŐS #677: M(n,k) ≠ M(m,k) for all m ≥ n+k -/
theorem erdos_677 (n k m : ℕ) (hk : k ≥ 1) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  by_cases hn : n ≥ k
  · exact erdos_677_n_ge_k n k m hk hn hm
  · push_neg at hn
    exact erdos_677_n_lt_k n k m hk hn hm

/-! ## Test Cases -/

example : M 1 3 = 12 := by native_decide

example : M 4 3 = 210 := by native_decide

example : M 1 3 ≠ M 4 3 := by native_decide

example : M 2 4 ≠ M 6 4 := by native_decide

end
