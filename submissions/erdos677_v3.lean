/-
Erdős Problem #677 - LCM of Consecutive Integers
VERSION 3: Contains YOUR OWN PROVEN LEMMAS (not axioms)

=== BUG FIX ===
sylvester_schur_weak (n≥1) was NEGATED - counterexample n=1, k=5
chain_or_growth was NEGATED - counterexample n=6, k=2, m=8
These have been REMOVED.

=== YOUR PROVEN WORK (included with full proofs) ===
All these lemmas have COMPLETE proofs from your v1 run.
They will typecheck, so you can build on them immediately!

=== TARGETS (still sorry) ===
1. sylvester_schur - CORRECT n≥k hypothesis
2. erdos_677 - main theorem
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Nat

/-- M(n,k) = lcm of k consecutive integers starting from n+1 -/
def M (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-! ## YOUR PROVEN LEMMAS (from v1) -/

/-- Product of k consecutive integers ≥ k! [YOU PROVED THIS] -/
lemma product_consecutive_ge_factorial (n k : ℕ) (hk : k ≥ 1) :
    (Finset.Ioc n (n + k)).prod id ≥ k.factorial := by
  have h_prod_ge_factorial : ∀ m : ℕ, (∏ i ∈ Finset.range k, (m + i + 1)) ≥ k ! := by
    intro m; induction hk <;> simp_all +decide [ Nat.factorial_succ, Finset.prod_range_succ ] ; nlinarith;
  convert h_prod_ge_factorial n |> le_trans <| le_of_eq _ using 1;
  refine' Finset.prod_bij ( fun x hx => n + x + 1 ) _ _ _ _ <;> aesop;
  · grind;
  · grind +ring;
  · exact ⟨ b - n - 1, by omega, by omega ⟩

/-- If p > k, at most one multiple of p in any k-length interval [YOU PROVED THIS] -/
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

/-- If p | j and j ∈ (n, n+k], then p | M(n,k) [YOU PROVED THIS] -/
lemma prime_divides_M_via_elem (n k j p : ℕ) (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hdiv : p ∣ j) : p ∣ M n k := by
  unfold M
  apply dvd_trans hdiv
  exact Finset.dvd_lcm hj

/-- m+k divides M(m,k) [YOU PROVED THIS] -/
lemma mk_divides_M (m k : ℕ) (hk : k ≥ 1) : m + k ∣ M m k := by
  unfold M
  exact Finset.dvd_lcm (by simp [Finset.mem_Ioc]; omega)

/-- M is positive [YOU PROVED THIS] -/
lemma M_pos (n k : ℕ) (hk : k ≥ 1) : M n k > 0 := by
  unfold M
  apply Finset.lcm_pos
  simp [Finset.Ioc_eq_empty_iff]
  omega

/-- FORBIDDEN ZONE - KEY STRUCTURAL THEOREM [YOU PROVED THIS - 40 lines!] -/
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

/-- Forbidden zone range corollary [YOU PROVED THIS] -/
lemma forbidden_zone_range (n k j p : ℕ) (hk : k ≥ 1)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hpk : p > k) (hpdiv : p ∣ j) :
    ∀ m, n + k ≤ m → m + k < j + p → M n k ≠ M m k := by
  intro m hm_lo hm_hi
  exact forbidden_zone n k j m p hk hj hp hpk hpdiv hm_lo hm_hi

/-- Next zone contains new multiple [YOU PROVED THIS] -/
lemma next_zone_contains_new_multiple (n k j m p : ℕ)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hm : m ≥ j + p - k) :
    j + p ∈ Finset.Ioc m (m + k) := by
  simp only [mem_Ioc] at hj ⊢
  omega

/-- For large m, M grows [YOU PROVED THIS] -/
lemma M_grows_large (n k m : ℕ) (hk : k ≥ 1) (hm : m + k > M n k) :
    M m k ≠ M n k := by
  intro heq
  have hdiv : m + k ∣ M m k := mk_divides_M m k hk
  rw [heq] at hdiv
  have hMpos : M n k > 0 := M_pos n k hk
  have : m + k ≤ M n k := Nat.le_of_dvd hMpos hdiv
  omega

/-- M upper bound [YOU PROVED THIS] -/
lemma M_upper_bound (n k : ℕ) (hk : k ≥ 1) :
    M n k ≤ (Finset.Ioc n (n + k)).prod id := by
  unfold M
  exact Finset.lcm_le_prod id (by simp) (by intro i hi; simp [mem_Ioc] at hi; omega)

/-! ## KEY TARGET: Sylvester-Schur with CORRECT hypothesis -/

/-- SYLVESTER-SCHUR: For n ≥ k ≥ 1, some element in [n+1, n+k] has a prime factor > k.

    The hypothesis n ≥ k is ESSENTIAL. You found counterexample for n ≥ 1:
    n=1, k=5 → {2,3,4,5,6} has NO prime factor > 5.

    With n ≥ k, the product (n+1)...(n+k) is large enough that primes > k must appear. -/
theorem sylvester_schur (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j := by
  -- Use product_consecutive_ge_factorial: product ≥ k!
  -- With n ≥ k, each factor > k, so product > k^k
  -- Prime counting shows primes ≤ k can't account for this
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
    · -- Past forbidden zone: new interval (m, m+k] contains j+p
      -- So p | M(m,k). Need to show M(n,k) ≠ M(m,k) by comparing prime powers
      push_neg at hlarge
      have h_contains : j + p ∈ Finset.Ioc m (m + k) := by
        simp only [mem_Ioc] at hj ⊢
        omega
      have hp_div_m : p ∣ M m k := prime_divides_M_via_elem m k (j + p) p h_contains hp (by
        exact dvd_add hpdiv (dvd_refl p))
      -- Key: analyze prime power structure to show inequality
      sorry

/-- Erdős #677 for n < k -/
theorem erdos_677_n_lt_k (n k m : ℕ) (hk : k ≥ 1) (hn : n < k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  -- For n < k: m ≥ n+k ≥ k, so apply sylvester_schur to m
  have hm_ge_k : m ≥ k := by omega
  obtain ⟨j, hj, p, hp, hpk, hpdiv⟩ := sylvester_schur m k hk hm_ge_k
  -- p | M(m,k) via j. If M(n,k) = M(m,k), then p | M(n,k)
  -- Where does p come from in (n, n+k]?
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
