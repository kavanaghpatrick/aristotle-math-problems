/-
Erdős Problem #677 - LCM of consecutive integers
GAP STRATEGY with Forbidden Zone

PROBLEM: Prove M(n,k) ≠ M(m,k) for all m ≥ n+k where M(n,k) = lcm(n+1,...,n+k)

FROM ERDOSPROBLEMS.COM:
- Thue-Siegel implies only finitely many exceptions for fixed k
- Known counterexamples M(4,3)=M(13,2) and M(3,4)=M(19,2) use DIFFERENT k values
- For SAME k, no counterexamples are known

KEY INSIGHT - THE GAP STRATEGY:
1. If p is a prime factor of n+k with p > k, then p appears UNIQUELY at n+k in [n+1,n+k]
2. The NEXT multiple of p after n+k is n+k+p
3. For m ∈ [n+k, n+p-1], no multiple of p is in [m+1, m+k]
4. So p | M(n,k) but p ∤ M(m,k) for these m → M(n,k) ≠ M(m,k)
5. For m ≥ n+p, use growth argument or iterate

SYLVESTER-SCHUR THEOREM: If n ≥ k, then ∏(n+1)...(n+k) has a prime factor > k.
This guarantees existence of such a prime p.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Nat

/-- M(n,k) = lcm of k consecutive integers starting from n+1 -/
def M (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-! ## Core Lemmas for Gap Strategy -/

/-- If p > k, then at most one multiple of p is in any interval of length k -/
lemma unique_multiple_of_large_prime (x k p : ℕ) (hp : p > k) :
    ∀ y₁ ∈ Finset.Ioc x (x + k), ∀ y₂ ∈ Finset.Ioc x (x + k),
    p ∣ y₁ → p ∣ y₂ → y₁ = y₂ := by
  intro y₁ hy₁ y₂ hy₂ hdiv₁ hdiv₂
  -- If y₁, y₂ are both multiples of p, then |y₁ - y₂| is a multiple of p
  -- But |y₁ - y₂| < k < p, so must have y₁ = y₂
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

/-- n+k is in the interval (n, n+k] -/
lemma nk_in_interval (n k : ℕ) (hk : k ≥ 1) : n + k ∈ Finset.Ioc n (n + k) := by
  simp [Finset.mem_Ioc]; omega

/-- If p | n+k and p > k, then p | M(n,k) via n+k -/
lemma large_prime_divides_M (n k p : ℕ) (hk : k ≥ 1) (hp : p.Prime) (hpk : p > k)
    (hpdiv : p ∣ n + k) : p ∣ M n k := by
  unfold M
  apply dvd_trans hpdiv
  exact Finset.dvd_lcm (nk_in_interval n k hk)

/-- KEY LEMMA: If p | n+k, p > k, and n+k < m+1, then for p to divide M(m,k),
    we need a multiple of p in (m, m+k]. The smallest such is ≥ n+k+p. -/
lemma next_multiple_after_nk (n k m p : ℕ) (hp : p.Prime) (hpk : p > k)
    (hpdiv : p ∣ n + k) (hm : m ≥ n + k) :
    (∃ y ∈ Finset.Ioc m (m + k), p ∣ y) → m + k ≥ n + k + p := by
  intro ⟨y, hy, hdiv⟩
  simp only [mem_Ioc] at hy
  obtain ⟨q, rfl⟩ := hdiv
  obtain ⟨r, rfl⟩ := hpdiv
  -- y = q * p, n + k = r * p
  -- y > m ≥ n + k = r * p, so q * p > r * p, so q > r, so q ≥ r + 1
  -- y ≤ m + k, so m + k ≥ q * p ≥ (r + 1) * p = r * p + p = n + k + p
  have hq_gt_r : q > r := by
    have : q * p > m := hy.1
    have : m ≥ r * p := hm
    nlinarith
  have hq_ge : q ≥ r + 1 := hq_gt_r
  calc m + k ≥ q * p := hy.2
    _ ≥ (r + 1) * p := by nlinarith
    _ = r * p + p := by ring
    _ = n + k + p := rfl

/-- THE FORBIDDEN ZONE: If p | n+k with p > k, and m ∈ [n+k, n+p-1],
    then p ∤ M(m,k), so M(n,k) ≠ M(m,k) -/
theorem forbidden_zone (n k m p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hpk : p > k) (hpdiv : p ∣ n + k) (hm_lo : m ≥ n + k) (hm_hi : m + k < n + k + p) :
    M n k ≠ M m k := by
  intro heq
  -- p | M(n,k)
  have hdiv_n : p ∣ M n k := large_prime_divides_M n k p hk hp hpk hpdiv
  -- So p | M(m,k)
  rw [heq] at hdiv_n
  -- This means ∃ y ∈ (m, m+k] with p | y
  unfold M at hdiv_n
  have hprime_dvd : ∃ y ∈ Finset.Ioc m (m + k), p ∣ y := by
    by_contra h
    push_neg at h
    -- If p doesn't divide any element, then p ∤ lcm
    have : Nat.Coprime p (Finset.Ioc m (m + k)).lcm id := by
      apply Nat.Coprime.symm
      apply Nat.coprime_of_dvd
      intro q hq_prime hq_dvd_lcm hq_dvd_p
      have hq_eq_p : q = p := (Nat.Prime.eq_one_or_self_of_dvd hp q hq_dvd_p).resolve_left
        (Nat.Prime.ne_one hq_prime)
      rw [hq_eq_p] at hq_dvd_lcm
      -- p | lcm means p | some element
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
  -- But by next_multiple_after_nk, this requires m + k ≥ n + k + p
  have hcontra := next_multiple_after_nk n k m p hp hpk hpdiv hm_lo hprime_dvd
  omega

/-! ## Existence of Large Prime Factor -/

/-- Sylvester-Schur: Product of k consecutive integers > k has a prime factor > k.
    More specifically, if n ≥ k, then n+k has a prime factor > k, OR some
    element in [n+1, n+k] does. -/
lemma exists_prime_gt_k_dividing_interval (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j := by
  sorry

/-- For n+k itself: if n+k > k, there's often a large prime factor -/
lemma exists_large_prime_factor_of_nk (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    (∃ p, p.Prime ∧ p > k ∧ p ∣ n + k) ∨
    (∃ j ∈ Finset.Ioc n (n + k - 1), ∃ p, p.Prime ∧ p > k ∧ p ∣ j) := by
  sorry

/-! ## Growth Argument for Large m -/

/-- M(m,k) grows with m: specifically, m+k | M(m,k) -/
lemma mk_divides_M (m k : ℕ) (hk : k ≥ 1) : m + k ∣ M m k := by
  unfold M
  exact Finset.dvd_lcm (nk_in_interval m k hk)

/-- For large enough m, M(m,k) > M(n,k) by size alone -/
lemma M_grows_large (n k m : ℕ) (hk : k ≥ 1) (hm : m + k > M n k) :
    M m k ≠ M n k := by
  intro heq
  have hdiv : m + k ∣ M m k := mk_divides_M m k hk
  rw [heq] at hdiv
  have : m + k ≤ M n k := Nat.le_of_dvd (by unfold M; simp [Finset.lcm_pos]) hdiv
  omega

/-! ## Main Theorem -/

/-- MAIN THEOREM: Erdős #677 -/
theorem erdos_677 (n k m : ℕ) (hk : k ≥ 1) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  -- Case 1: m is very large (m + k > M(n,k))
  by_cases hlarge : m + k > M n k
  · exact M_grows_large n k m hk hlarge
  · push_neg at hlarge
    -- Case 2: Use the gap strategy with a large prime
    -- Find a prime p > k dividing some element in [n+1, n+k]
    sorry

/-! ## Verified Test Cases -/

theorem M_4_3 : M 4 3 = 210 := by native_decide
theorem M_13_2 : M 13 2 = 210 := by native_decide  -- Different k!
theorem M_differs_same_k : M 1 2 ≠ M 3 2 := by native_decide
theorem M_differs_same_k2 : M 2 3 ≠ M 5 3 := by native_decide

-- Verify the known "counterexamples" are with different k
theorem different_k_example : M 4 3 = M 13 2 := by native_decide

end
