/-
Erdős Problem #677 - LCM of Consecutive Integers
ENHANCED SCAFFOLDING

PROBLEM: Prove M(n,k) ≠ M(m,k) for all m ≥ n+k where M(n,k) = lcm(n+1,...,n+k)

ENHANCED: Added intermediate lemmas for:
1. Chain of forbidden zones (iteration)
2. Base cases for small k
3. Better n < k handling
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Nat

/-- M(n,k) = lcm of k consecutive integers starting from n+1 -/
def M (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-! ## Sylvester-Schur Theorem -/

/-- Product of k consecutive integers ≥ k! -/
lemma product_consecutive_ge_factorial (n k : ℕ) (hk : k ≥ 1) :
    (Finset.Ioc n (n + k)).prod id ≥ k.factorial := by
  -- Product (n+1)...(n+k) ≥ k! by comparing term-by-term
  sorry

/-- SYLVESTER-SCHUR: For n ≥ k ≥ 1, some element in [n+1, n+k] has a prime factor > k. -/
theorem sylvester_schur (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j := by
  -- The product (n+1)...(n+k) has a prime factor > k
  -- Proof: product ≥ k! and can't be entirely composed of primes ≤ k
  -- when n ≥ k (by prime counting arguments)
  sorry

/-- For any n ≥ 1, there exists j ∈ [n+1, n+k] and prime p > k with p | j -/
theorem sylvester_schur_weak (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j := by
  -- Weaker version that still suffices for most cases
  sorry

/-! ## Core Gap Lemmas -/

/-- If p > k, then at most one multiple of p is in any interval of length k -/
lemma unique_multiple_of_large_prime (x k p : ℕ) (hp : p > k) :
    ∀ y₁ ∈ Finset.Ioc x (x + k), ∀ y₂ ∈ Finset.Ioc x (x + k),
    p ∣ y₁ → p ∣ y₂ → y₁ = y₂ := by
  intro y₁ hy₁ y₂ hy₂ hdiv₁ hdiv₂
  simp only [mem_Ioc] at hy₁ hy₂
  obtain ⟨a, rfl⟩ := hdiv₁
  obtain ⟨b, rfl⟩ := hdiv₂
  -- If a*p, b*p both in (x, x+k], then |a-b| * p < k
  -- Since p > k, we must have a = b
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

/-- If p | j and j ∈ (n, n+k], then p | M(n,k) -/
lemma prime_divides_M_via_elem (n k j p : ℕ) (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hdiv : p ∣ j) : p ∣ M n k := by
  unfold M
  apply dvd_trans hdiv
  exact Finset.dvd_lcm hj

/-- m+k divides M(m,k) -/
lemma mk_divides_M (m k : ℕ) (hk : k ≥ 1) : m + k ∣ M m k := by
  unfold M
  exact Finset.dvd_lcm (by simp [Finset.mem_Ioc]; omega)

/-- M is positive -/
lemma M_pos (n k : ℕ) (hk : k ≥ 1) : M n k > 0 := by
  unfold M
  apply Finset.lcm_pos
  simp [Finset.Ioc_eq_empty_iff]
  omega

/-! ## The Forbidden Zone Theorem -/

/-- FORBIDDEN ZONE: If j ∈ [n+1, n+k] has prime p > k with p | j,
    and m is in the range where no multiple of p is in [m+1, m+k],
    then M(n,k) ≠ M(m,k) -/
theorem forbidden_zone (n k j m p : ℕ) (hk : k ≥ 1)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hpk : p > k) (hpdiv : p ∣ j)
    (hm_lo : m ≥ n + k) (hm_hi : m + k < j + p) :
    M n k ≠ M m k := by
  intro heq
  -- p | M(n,k) via j
  have hdiv_n : p ∣ M n k := prime_divides_M_via_elem n k j p hj hp hpdiv
  -- So p | M(m,k)
  rw [heq] at hdiv_n
  -- This means ∃ y ∈ (m, m+k] with p | y
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
  -- But any multiple of p in (m, m+k] would need to be ≥ j + p
  obtain ⟨y, hy_mem, hy_div⟩ := hprime_dvd
  simp only [mem_Ioc] at hy_mem hj
  obtain ⟨a, rfl⟩ := hpdiv
  obtain ⟨b, rfl⟩ := hy_div
  -- y = b*p > m ≥ n+k ≥ j = a*p, so b > a, so b ≥ a+1
  -- y = b*p ≥ (a+1)*p = j + p > m + k. Contradiction.
  have hb_gt_a : b > a := by
    have h1 : b * p > m := hy_mem.1
    have h2 : m ≥ a * p := by
      have : a * p ≤ n + k := hj.2
      omega
    nlinarith
  have : b * p ≥ (a + 1) * p := by nlinarith
  have : b * p ≥ a * p + p := by ring_nf; ring_nf at this; exact this
  omega

/-! ## Chaining Forbidden Zones -/

/-- The forbidden zone for (j, p) covers m in [n+k, j+p-k-1] -/
lemma forbidden_zone_range (n k j p : ℕ) (hk : k ≥ 1)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hpk : p > k) (hpdiv : p ∣ j) :
    ∀ m, n + k ≤ m → m + k < j + p → M n k ≠ M m k := by
  intro m hm_lo hm_hi
  exact forbidden_zone n k j m p hk hj hp hpk hpdiv hm_lo hm_hi

/-- After the forbidden zone, the next interval [m+1, m+k] contains j+p -/
lemma next_zone_contains_new_multiple (n k j m p : ℕ)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hm : m ≥ j + p - k) :
    j + p ∈ Finset.Ioc m (m + k) := by
  simp only [mem_Ioc] at hj ⊢
  omega

/-- Chaining: After forbidden zone ends, either growth kicks in or we find new prime -/
lemma chain_or_growth (n k m : ℕ) (hk : k ≥ 1) (hn : n ≥ k) (hm : m ≥ n + k) :
    m + k > M n k ∨
    ∃ j' ∈ Finset.Ioc m (m + k), ∃ p', p'.Prime ∧ p' > k ∧ p' ∣ j' ∧
      ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j ∧ p' ∣ M n k := by
  -- Either m+k > M(n,k) directly, or we can find structure in [m+1, m+k]
  sorry

/-! ## Growth Argument for Large m -/

/-- For large enough m, M(m,k) > M(n,k) by size alone -/
lemma M_grows_large (n k m : ℕ) (hk : k ≥ 1) (hm : m + k > M n k) :
    M m k ≠ M n k := by
  intro heq
  have hdiv : m + k ∣ M m k := mk_divides_M m k hk
  rw [heq] at hdiv
  have hMpos : M n k > 0 := M_pos n k hk
  have : m + k ≤ M n k := Nat.le_of_dvd hMpos hdiv
  omega

/-- M(n,k) is bounded: M(n,k) ≤ (n+k)! / n! -/
lemma M_upper_bound (n k : ℕ) (hk : k ≥ 1) :
    M n k ≤ (Finset.Ioc n (n + k)).prod id := by
  unfold M
  exact Finset.lcm_le_prod id (by simp) (by intro i hi; simp [mem_Ioc] at hi; omega)

/-! ## Main Theorem -/

/-- MAIN THEOREM: Erdős #677 for n ≥ k -/
theorem erdos_677_n_ge_k (n k m : ℕ) (hk : k ≥ 1) (hn : n ≥ k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  -- Get j and p from Sylvester-Schur
  obtain ⟨j, hj, p, hp, hpk, hpdiv⟩ := sylvester_schur n k hk hn
  -- Induction on m, using forbidden zones and growth
  -- Each forbidden zone covers [n+k, j+p-k-1]
  -- After that, either growth or new prime extends the argument
  by_cases hzone : m + k < j + p
  · exact forbidden_zone n k j m p hk hj hp hpk hpdiv hm hzone
  · push_neg at hzone
    by_cases hlarge : m + k > M n k
    · exact M_grows_large n k m hk hlarge
    · -- Need iteration: the new interval has a new prime
      -- This is the key technical step
      sorry

/-- MAIN THEOREM: Erdős #677 for n < k (base cases) -/
theorem erdos_677_n_lt_k (n k m : ℕ) (hk : k ≥ 1) (hn : n < k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  -- For n < k, use direct properties or weak Sylvester-Schur
  -- The interval [n+1, n+k] contains [1, k] when n=0
  -- So it definitely has primes > n but we need primes > k
  -- Alternative: use that M(n,k) grows monotonically in n for fixed k
  sorry

/-- MAIN THEOREM: Erdős #677 general case -/
theorem erdos_677 (n k m : ℕ) (hk : k ≥ 1) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  by_cases hn : n ≥ k
  · exact erdos_677_n_ge_k n k m hk hn hm
  · push_neg at hn
    exact erdos_677_n_lt_k n k m hk hn hm

/-! ## Test Cases -/

theorem test_M_1_3 : M 1 3 = 12 := by native_decide
theorem test_M_4_3 : M 4 3 = 210 := by native_decide
theorem test_same_k_differ : M 1 3 ≠ M 4 3 := by native_decide
theorem test_same_k_differ2 : M 2 4 ≠ M 6 4 := by native_decide

end
