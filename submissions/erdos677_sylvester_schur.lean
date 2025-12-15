/-
Erdős Problem #677 - LCM of Consecutive Integers
CORRECTED VERSION with proper Sylvester-Schur

PROBLEM: Prove M(n,k) ≠ M(m,k) for all m ≥ n+k where M(n,k) = lcm(n+1,...,n+k)

KEY FIX: Previous version wrongly claimed n+k always has prime factor > k.
COUNTEREXAMPLE: n=1, k=8 gives n+k=9=3², no prime > 8.

SYLVESTER-SCHUR THEOREM (1892/1929):
For n ≥ k, the product (n+1)(n+2)...(n+k) has a prime factor > k.
Equivalently: SOME element j ∈ [n+1, n+k] has a prime factor > k.

PROOF STRATEGY:
1. Use Sylvester-Schur to find j ∈ [n+1, n+k] with prime p > k dividing j
2. p | M(n,k) since j | lcm
3. For m in "forbidden zone" [n+k, n+j+p-k-1], p ∤ M(m,k)
4. For large m, use growth argument: m+k | M(m,k) > M(n,k)

CASE n < k: Handle separately - may need different argument or base cases
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Nat

/-- M(n,k) = lcm of k consecutive integers starting from n+1 -/
def M (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-! ## Sylvester-Schur Theorem -/

/-- SYLVESTER-SCHUR: For n ≥ k ≥ 1, some element in [n+1, n+k] has a prime factor > k.
    This is the corrected version - we don't claim n+k specifically has such a factor. -/
theorem sylvester_schur (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j := by
  -- The product (n+1)...(n+k) has a prime factor > k
  -- So some factor j in the range has a prime divisor > k
  sorry

/-! ## Core Gap Lemmas (Previously Proven) -/

/-- If p > k, then at most one multiple of p is in any interval of length k -/
lemma unique_multiple_of_large_prime (x k p : ℕ) (hp : p > k) :
    ∀ y₁ ∈ Finset.Ioc x (x + k), ∀ y₂ ∈ Finset.Ioc x (x + k),
    p ∣ y₁ → p ∣ y₂ → y₁ = y₂ := by
  intro y₁ hy₁ y₂ hy₂ hdiv₁ hdiv₂
  simp only [mem_Ioc] at hy₁ hy₂
  obtain ⟨a, rfl⟩ := hdiv₁
  obtain ⟨b, rfl⟩ := hdiv₂
  have hab : (a : ℤ) * p - b * p = (a - b) * p := by ring
  have hbound : |((a : ℤ) - b) * p| < k := by
    have h1 : (a : ℤ) * p ≤ x + k := by exact_mod_cast hy₁.2
    have h2 : (b : ℤ) * p ≤ x + k := by exact_mod_cast hy₂.2
    have h3 : (a : ℤ) * p > x := by exact_mod_cast hy₁.1
    have h4 : (b : ℤ) * p > x := by exact_mod_cast hy₂.1
    calc |((a : ℤ) - b) * p| = |(a : ℤ) * p - b * p| := by ring_nf
      _ < k := by nlinarith
  have hp_pos : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (by omega : p ≠ 0)
  have : |(a : ℤ) - b| * p < k := by
    rw [abs_mul] at hbound
    simp only [abs_of_pos hp_pos] at hbound
    exact hbound
  have hab_zero : (a : ℤ) - b = 0 := by
    by_contra h
    have : |(a : ℤ) - b| ≥ 1 := by
      rw [abs_sub_comm]
      exact Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
    nlinarith
  omega

/-- j ∈ (n, n+k] -/
lemma elem_in_interval (n k j : ℕ) (hj_lo : j > n) (hj_hi : j ≤ n + k) :
    j ∈ Finset.Ioc n (n + k) := by
  simp [Finset.mem_Ioc]; omega

/-- If p | j and j ∈ (n, n+k], then p | M(n,k) -/
lemma prime_divides_M_via_elem (n k j p : ℕ) (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hdiv : p ∣ j) : p ∣ M n k := by
  unfold M
  apply dvd_trans hdiv
  exact Finset.dvd_lcm hj

/-- Next multiple of p after j is j+p -/
lemma next_multiple (j p m : ℕ) (hp : p.Prime) (hdiv : p ∣ j) (hm : m > j) :
    (∃ y, m < y ∧ y ≤ m + p - 1 ∧ p ∣ y) → False := by
  intro ⟨y, hy_lo, hy_hi, hy_div⟩
  obtain ⟨a, rfl⟩ := hdiv
  obtain ⟨b, rfl⟩ := hy_div
  -- y = b*p > m > j = a*p, so b > a
  -- y ≤ m + p - 1 < j + p = (a+1)*p
  -- So b*p < (a+1)*p, meaning b < a+1, i.e., b ≤ a. Contradiction.
  have hb_gt_a : b > a := by
    have : b * p > a * p := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hb_lt : b * p < (a + 1) * p := by
    have hp_pos : p ≥ 1 := hp.one_lt.le
    calc b * p ≤ m + p - 1 := hy_hi
      _ < a * p + p := by omega
      _ = (a + 1) * p := by ring
  have : b < a + 1 := Nat.lt_of_mul_lt_mul_right hb_lt
  omega

/-! ## The Forbidden Zone Theorem -/

/-- FORBIDDEN ZONE: If j ∈ [n+1, n+k] has prime p > k with p | j,
    and m is in the range where no multiple of p is in [m+1, m+k],
    then M(n,k) ≠ M(m,k) -/
theorem forbidden_zone_general (n k j m p : ℕ) (hk : k ≥ 1)
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
  unfold M at hdiv_n
  have hprime_dvd : ∃ y ∈ Finset.Ioc m (m + k), p ∣ y := by
    by_contra h
    push_neg at h
    have : Nat.Coprime p (Finset.Ioc m (m + k)).lcm id := by
      apply Nat.Coprime.symm
      apply Nat.coprime_of_dvd
      intro q hq_prime hq_dvd_lcm hq_dvd_p
      have hq_eq_p : q = p := (Nat.Prime.eq_one_or_self_of_dvd hp q hq_dvd_p).resolve_left
        (Nat.Prime.ne_one hq_prime)
      rw [hq_eq_p] at hq_dvd_lcm
      have : ∃ x ∈ Finset.Ioc m (m + k), p ∣ x := by
        by_contra hall
        push_neg at hall
        have hcop : ∀ x ∈ Finset.Ioc m (m + k), Nat.Coprime p x := by
          intro x hx
          exact hp.coprime_iff_not_dvd.mpr (hall x hx)
        have : Nat.Coprime p ((Finset.Ioc m (m + k)).lcm id) := by
          apply Nat.Coprime.symm
          apply Finset.coprime_lcm
          intro x hx
          exact (hcop x hx).symm
        exact Nat.not_coprime_of_dvd_of_dvd (hp.one_lt) hq_dvd_lcm (dvd_refl p) this.symm
      exact h this
    exact Nat.not_coprime_of_dvd_of_dvd (hp.one_lt) hdiv_n (dvd_refl p) this.symm
  -- But any multiple of p in (m, m+k] would need to be ≥ j + p
  obtain ⟨y, hy_mem, hy_div⟩ := hprime_dvd
  simp only [mem_Ioc] at hy_mem hj
  obtain ⟨a, rfl⟩ := hpdiv
  obtain ⟨b, rfl⟩ := hy_div
  -- j = a*p ∈ (n, n+k], y = b*p ∈ (m, m+k]
  -- y > m ≥ n+k ≥ j = a*p, so b*p > a*p, so b > a, so b ≥ a+1
  -- y = b*p ≥ (a+1)*p = j + p > m + k. Contradiction with y ≤ m+k.
  have hb_gt_a : b > a := by
    have : b * p > m := hy_mem.1
    have : m ≥ a * p := by
      have : a * p ≤ n + k := hj.2
      omega
    nlinarith
  have : b * p ≥ (a + 1) * p := by nlinarith
  have : b * p ≥ a * p + p := by ring_nf; ring_nf at this; exact this
  have : y ≥ j + p := this
  omega

/-! ## Growth Argument for Large m -/

/-- m+k divides M(m,k) -/
lemma mk_divides_M (m k : ℕ) (hk : k ≥ 1) : m + k ∣ M m k := by
  unfold M
  exact Finset.dvd_lcm (by simp [Finset.mem_Ioc]; omega)

/-- For large enough m, M(m,k) > M(n,k) by size alone -/
lemma M_grows_large (n k m : ℕ) (hk : k ≥ 1) (hm : m + k > M n k) :
    M m k ≠ M n k := by
  intro heq
  have hdiv : m + k ∣ M m k := mk_divides_M m k hk
  rw [heq] at hdiv
  have hMpos : M n k > 0 := by unfold M; simp [Finset.lcm_pos]
  have : m + k ≤ M n k := Nat.le_of_dvd hMpos hdiv
  omega

/-! ## Main Theorem -/

/-- MAIN THEOREM: Erdős #677 for n ≥ k -/
theorem erdos_677_n_ge_k (n k m : ℕ) (hk : k ≥ 1) (hn : n ≥ k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  -- Get j and p from Sylvester-Schur
  obtain ⟨j, hj, p, hp, hpk, hpdiv⟩ := sylvester_schur n k hk hn
  -- Case split on whether m is in forbidden zone or beyond
  by_cases hzone : m + k < j + p
  · -- Forbidden zone case
    exact forbidden_zone_general n k j m p hk hj hp hpk hpdiv hm hzone
  · -- Large m case - use growth or iterate
    push_neg at hzone
    -- Either m+k > M(n,k) (growth), or we need to iterate the argument
    by_cases hlarge : m + k > M n k
    · exact M_grows_large n k m hk hlarge
    · -- Need more sophisticated argument here
      -- The forbidden zone extends to j+p-k-1, and beyond that we have new intervals
      sorry

/-- MAIN THEOREM: Erdős #677 general case -/
theorem erdos_677 (n k m : ℕ) (hk : k ≥ 1) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  by_cases hn : n ≥ k
  · exact erdos_677_n_ge_k n k m hk hn hm
  · -- Case n < k: need different approach
    -- For small n, we may be able to use direct computation or weaker bounds
    push_neg at hn
    sorry

/-! ## Test Cases -/

theorem test_M_1_3 : M 1 3 = 12 := by native_decide
theorem test_M_4_3 : M 4 3 = 210 := by native_decide
theorem test_M_13_2 : M 13 2 = 210 := by native_decide  -- Same as M(4,3) but different k!

-- Key test: same k values should differ
theorem test_same_k_differ : M 1 3 ≠ M 4 3 := by native_decide
theorem test_same_k_differ2 : M 2 4 ≠ M 6 4 := by native_decide

end
