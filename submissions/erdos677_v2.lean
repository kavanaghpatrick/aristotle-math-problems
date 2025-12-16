/-
Erdős Problem #677 - LCM of Consecutive Integers
VERSION 2: Fixed hypothesis + Aristotle's own proven results as axioms

=== BUG FIX FROM v1 ===
sylvester_schur_weak had hypothesis n ≥ 1, but REAL theorem needs n ≥ k.
Aristotle found counterexample: n=1, k=5 → interval {2,3,4,5,6} has no prime > 5.
  - 2 = 2 (prime 2 ≤ 5)
  - 3 = 3 (prime 3 ≤ 5)
  - 4 = 2² (prime 2 ≤ 5)
  - 5 = 5 (prime 5 ≤ 5)
  - 6 = 2×3 (primes 2,3 ≤ 5)

=== AXIOMS FROM v1 (Your own proven results!) ===
All these were PROVED by you. Build on them!
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Nat

/-- M(n,k) = lcm of k consecutive integers starting from n+1 -/
def M (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-! ## AXIOMS: Your proven results from v1 -/

/-- AXIOM 1: Product of k consecutive integers ≥ k!
    You proved this with induction! -/
axiom product_consecutive_ge_factorial (n k : ℕ) (hk : k ≥ 1) :
    (Finset.Ioc n (n + k)).prod id ≥ k.factorial

/-- AXIOM 2: If p > k, at most one multiple of p in any k-length interval
    You proved this with nlinarith! -/
axiom unique_multiple_of_large_prime (x k p : ℕ) (hp : p > k) :
    ∀ y₁ ∈ Finset.Ioc x (x + k), ∀ y₂ ∈ Finset.Ioc x (x + k),
    p ∣ y₁ → p ∣ y₂ → y₁ = y₂

/-- AXIOM 3: If p | j and j ∈ (n, n+k], then p | M(n,k)
    You proved this via Finset.dvd_lcm! -/
axiom prime_divides_M_via_elem (n k j p : ℕ) (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hdiv : p ∣ j) : p ∣ M n k

/-- AXIOM 4: m+k divides M(m,k)
    You proved this directly! -/
axiom mk_divides_M (m k : ℕ) (hk : k ≥ 1) : m + k ∣ M m k

/-- AXIOM 5: M is positive
    You proved this via Finset.lcm_pos! -/
axiom M_pos (n k : ℕ) (hk : k ≥ 1) : M n k > 0

/-- AXIOM 6: FORBIDDEN ZONE - The key structural theorem!
    If j ∈ [n+1, n+k] has prime p > k with p | j,
    and m is in the range where no multiple of p is in [m+1, m+k],
    then M(n,k) ≠ M(m,k)

    You proved this with 180+ lines! -/
axiom forbidden_zone (n k j m p : ℕ) (hk : k ≥ 1)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hpk : p > k) (hpdiv : p ∣ j)
    (hm_lo : m ≥ n + k) (hm_hi : m + k < j + p) :
    M n k ≠ M m k

/-- AXIOM 7: Corollary of forbidden_zone
    You proved this! -/
axiom forbidden_zone_range (n k j p : ℕ) (hk : k ≥ 1)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hp : p.Prime) (hpk : p > k) (hpdiv : p ∣ j) :
    ∀ m, n + k ≤ m → m + k < j + p → M n k ≠ M m k

/-! ## KEY TARGET: Sylvester-Schur with CORRECT hypothesis -/

/-- SYLVESTER-SCHUR: For n ≥ k ≥ 1, some element in [n+1, n+k] has a prime factor > k.

    THIS IS THE KEY LEMMA. The correct hypothesis is n ≥ k (not n ≥ 1).

    Proof idea: The product (n+1)...(n+k) has k terms, each > n ≥ k.
    This product is large (≥ k!). If all prime factors were ≤ k, the product
    would be bounded by (k!)^something, but with n ≥ k the product exceeds this.

    Classical proof uses Chebyshev's bounds on prime counting. -/
theorem sylvester_schur (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j := by
  -- The product (n+1)...(n+k) ≥ k! by product_consecutive_ge_factorial
  -- Each factor > n ≥ k, so product > k^k
  -- If all prime factors were ≤ k, would need product ≤ (primorial k)^(log product)
  -- This contradicts the size bound for n ≥ k
  sorry

/-! ## Helper Lemmas for Main Theorem -/

/-- For large enough m, M(m,k) > M(n,k) by size alone -/
lemma M_grows_large (n k m : ℕ) (hk : k ≥ 1) (hm : m + k > M n k) :
    M m k ≠ M n k := by
  intro heq
  have hdiv : m + k ∣ M m k := mk_divides_M m k hk
  rw [heq] at hdiv
  have hMpos : M n k > 0 := M_pos n k hk
  have : m + k ≤ M n k := Nat.le_of_dvd hMpos hdiv
  omega

/-- M(n,k) is bounded by the product -/
lemma M_upper_bound (n k : ℕ) (hk : k ≥ 1) :
    M n k ≤ (Finset.Ioc n (n + k)).prod id := by
  unfold M
  exact Finset.lcm_le_prod id (by simp) (by intro i hi; simp [mem_Ioc] at hi; omega)

/-- After the forbidden zone, the next interval contains j+p -/
lemma next_zone_contains_new_multiple (n k j m p : ℕ)
    (hj : j ∈ Finset.Ioc n (n + k))
    (hm : m ≥ j + p - k) :
    j + p ∈ Finset.Ioc m (m + k) := by
  simp only [mem_Ioc] at hj ⊢
  omega

/-! ## MAIN THEOREM: Erdős #677 -/

/-- MAIN THEOREM for n ≥ k case (uses Sylvester-Schur directly) -/
theorem erdos_677_n_ge_k (n k m : ℕ) (hk : k ≥ 1) (hn : n ≥ k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  -- Get j and p from Sylvester-Schur
  obtain ⟨j, hj, p, hp, hpk, hpdiv⟩ := sylvester_schur n k hk hn
  -- Case split: is m in the forbidden zone?
  by_cases hzone : m + k < j + p
  · -- m is in forbidden zone - use AXIOM 6
    exact forbidden_zone n k j m p hk hj hp hpk hpdiv hm hzone
  · -- m is past forbidden zone
    push_neg at hzone
    -- Either m is so large that M grows
    by_cases hlarge : m + k > M n k
    · exact (M_grows_large n k m hk hlarge).symm
    · -- Key insight: past forbidden zone, new interval has j+p
      -- which means p | M(m,k), and we can iterate the argument
      push_neg at hlarge
      -- The new interval (m, m+k] contains j+p
      have h_contains : j + p ∈ Finset.Ioc m (m + k) := by
        simp only [mem_Ioc] at hj ⊢
        constructor
        · omega
        · -- m + k ≥ j + p from hzone
          omega
      -- So p | M(m,k)
      have hp_div_m : p ∣ M m k := prime_divides_M_via_elem m k (j + p) p h_contains hp (by
        exact dvd_add hpdiv (dvd_refl p))
      -- Key: M(m,k) has strictly more prime power factors than M(n,k)
      -- because m+k ≥ j+p and the new multiple j+p may have higher powers
      -- This leads to M(m,k) > M(n,k) or a new forbidden zone
      sorry

/-- For n < k, we need a different approach -/
theorem erdos_677_n_lt_k (n k m : ℕ) (hk : k ≥ 1) (hn : n < k) (hm : m ≥ n + k) :
    M n k ≠ M m k := by
  -- For n < k, the interval [n+1, n+k] always contains primes up to n+k
  -- and since n+k ≥ k+1 > k, we have primes > k when n+k is large enough
  --
  -- Alternative approach: For small n, directly compute or use that
  -- m ≥ n+k means m ≥ k, so we can apply sylvester_schur to m instead!
  --
  -- If m ≥ k, then [m+1, m+k] has a prime > k by Sylvester-Schur,
  -- so M(m,k) has a prime factor > k.
  -- If M(n,k) = M(m,k), then M(n,k) also has this prime factor.
  -- But where does it come from in [n+1, n+k] when n < k?
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
