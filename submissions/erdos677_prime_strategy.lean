/-
Erdős Problem #677 - LCM of consecutive integers
PRIME-BASED STRATEGY

CONJECTURE: For m ≥ n + k, lcm(n+1,...,n+k) ≠ lcm(m+1,...,m+k)

KEY INSIGHT: Use the largest prime in the interval.
- By Bertrand's postulate, ∃ prime p ∈ (n+k/2, n+k] for n+k ≥ 2
- This prime p appears exactly ONCE in [n+1, n+k] (as itself)
- For m ≥ n+k, we have p < m+1, so p ∉ [m+1, m+k]
- If 2p > m+k, then NO multiple of p is in [m+1, m+k]
- So p | lcmInterval(n,k) but p ∤ lcmInterval(m,k)
- Therefore lcmInterval(n,k) ≠ lcmInterval(m,k)

The condition 2p > m+k holds when:
- p > (n+k)/2 (from Bertrand)
- m = n+k (minimum gap)
- Then 2p > n+k = m, and we need 2p > m+k = n+2k
- This works when n ≥ k (sufficient but not necessary)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Nat

/-- LCM of k consecutive integers starting from n+1 -/
def lcmInterval (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-! ## Bertrand's Postulate and Prime Lemmas -/

/-- Bertrand's postulate: For n ≥ 1, there exists a prime p with n < p ≤ 2n.
    This should be in Mathlib as `Nat.exists_prime_lt_and_le_two_mul` or similar. -/
lemma bertrand_postulate (n : ℕ) (hn : n ≥ 1) :
    ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  sorry

/-- For n+k ≥ 2, there's a prime in ((n+k)/2, n+k] -/
lemma exists_large_prime_in_interval (n k : ℕ) (hk : k ≥ 1) (hnk : n + k ≥ 2) :
    ∃ p, p.Prime ∧ (n + k) / 2 < p ∧ p ≤ n + k := by
  -- Apply Bertrand to (n+k)/2
  sorry

/-- A prime p > n+k/2 appears at most once in [n+1, n+k] -/
lemma large_prime_unique_in_interval (n k p : ℕ) (hp : p.Prime)
    (hlarge : (n + k) / 2 < p) (hle : p ≤ n + k) :
    ∀ x ∈ Finset.Ioc n (n + k), p ∣ x → x = p := by
  intro x hx hdiv
  -- Since p > (n+k)/2 and x ≤ n+k, the only multiple of p in range is p itself
  sorry

/-- If p ≤ n+k and m ≥ n+k, then p < m+1, so p is not in [m+1, m+k] -/
lemma prime_not_in_shifted_interval (n k m p : ℕ)
    (hle : p ≤ n + k) (hm : m ≥ n + k) :
    p ∉ Finset.Ioc m (m + k) := by
  simp [Finset.mem_Ioc]
  intro h
  omega

/-- Key lemma: If p > (n+k)/2 and m ≥ n+k, and 2p > m+k, then p doesn't divide
    any element in [m+1, m+k] -/
lemma large_prime_not_dividing_shifted (n k m p : ℕ) (hp : p.Prime)
    (hlarge : (n + k) / 2 < p) (hle : p ≤ n + k) (hm : m ≥ n + k)
    (h2p : 2 * p > m + k) :
    ∀ x ∈ Finset.Ioc m (m + k), ¬(p ∣ x) := by
  intro x hx hdiv
  -- x ∈ (m, m+k], and p | x
  -- Since p ≤ n+k ≤ m < m+1 ≤ x, we have x ≥ p
  -- The smallest multiple of p greater than m is ⌈(m+1)/p⌉ * p
  -- Since p ≤ m, this is at least 2p
  -- But 2p > m+k ≥ x, contradiction
  sorry

/-- p divides lcmInterval(n,k) iff p divides some element in (n, n+k] -/
lemma prime_dvd_lcmInterval_iff (n k p : ℕ) (hp : p.Prime) :
    p ∣ lcmInterval n k ↔ ∃ x ∈ Finset.Ioc n (n + k), p ∣ x := by
  unfold lcmInterval
  constructor
  · intro hdiv
    -- If p | lcm S, then p | some element of S
    sorry
  · intro ⟨x, hx, hdiv⟩
    -- If p | x ∈ S, then p | lcm S
    sorry

/-! ## Main Theorem -/

/-- Sufficient condition: When n ≥ k, the large prime argument works -/
theorem erdos_677_sufficient (n k m : ℕ) (hk : k ≥ 1) (hn : n ≥ k) (hm : m ≥ n + k) :
    lcmInterval m k ≠ lcmInterval n k := by
  -- Get large prime p ∈ ((n+k)/2, n+k]
  have hnk : n + k ≥ 2 := by omega
  obtain ⟨p, hp_prime, hp_large, hp_le⟩ := exists_large_prime_in_interval n k hk hnk
  -- Show p | lcmInterval n k
  have hdiv_n : p ∣ lcmInterval n k := by
    rw [prime_dvd_lcmInterval_iff _ _ _ hp_prime]
    use p
    constructor
    · simp [Finset.mem_Ioc]; omega
    · exact dvd_refl p
  -- Show p ∤ lcmInterval m k
  have hndiv_m : ¬(p ∣ lcmInterval m k) := by
    rw [prime_dvd_lcmInterval_iff _ _ _ hp_prime]
    push_neg
    apply large_prime_not_dividing_shifted n k m p hp_prime hp_large hp_le hm
    -- Need 2p > m + k
    -- We have p > (n+k)/2, so 2p > n+k
    -- We have m ≥ n+k and n ≥ k, so m+k ≥ n+2k
    -- Need 2p > m+k ≥ n+2k... this needs more careful analysis
    sorry
  -- Conclude inequality
  intro heq
  rw [heq] at hdiv_n
  exact hndiv_m hdiv_n

/-- MAIN THEOREM: Erdős #677 -/
theorem erdos_677 :
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k := by
  intro m n k hk hm
  -- Case split on n ≥ k vs n < k
  by_cases hn : n ≥ k
  · exact erdos_677_sufficient n k m hk hn hm
  · -- Small n case: need different argument
    push_neg at hn
    sorry

/-! ## Verified Test Cases -/

theorem lcm_test_1 : lcmInterval 4 3 = 210 := by native_decide
theorem lcm_test_2 : lcmInterval 13 2 = 210 := by native_decide  -- Different k!
theorem lcm_test_3 : lcmInterval 1 2 ≠ lcmInterval 3 2 := by native_decide
theorem lcm_test_4 : lcmInterval 2 3 ≠ lcmInterval 5 3 := by native_decide

end
