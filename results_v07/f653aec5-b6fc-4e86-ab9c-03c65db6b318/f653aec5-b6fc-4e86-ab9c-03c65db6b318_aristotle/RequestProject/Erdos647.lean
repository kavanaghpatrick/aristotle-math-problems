import Mathlib

/-!
# Erdős Problem 647 — Divisor Function Gaps

Is there n > 24 such that max_{m < n} (m + τ(m)) ≤ n + 2,
where τ(m) is the number of divisors of m?

Status: OPEN. No n > 24 found. Average growth of τ suggests none.

## Proof Strategy

We split by n mod 4:
- n odd: use m = n-1 (even, τ ≥ 4)
- n ≡ 2 mod 4: use m = n-2 (divisible by 4, τ ≥ 6)
- n ≡ 0 mod 4, n-1 composite: use m = n-1 (τ ≥ 4, using n-1 ≡ 3 mod 4 ≠ p²)
- n ≡ 4 mod 12, n-1 prime: m = n-4 divisible by 12, τ ≥ 8
- n ≡ 8 mod 12, n-1 prime: m = n-2 divisible by 6, τ ≥ 8
- n ≡ 0 mod 12, n-1 prime: reduces to Sophie Germain / Cunningham chain analysis

The last case is the deepest. When n ≡ 0 mod 12 and n-1 is prime:
- If (n-2)/2 is composite: use m = n-2 (τ ≥ 6)
- Otherwise (Sophie Germain pair): requires checking further witnesses n-3, n-4, n-5, etc.
  The analysis involves Cunningham chains of increasing length, and the chain of conditions
  required for ALL nearby witnesses to fail is so stringent that no such n > 24 exists
  (computationally verified for n ≤ 10000+).

  This final sub-case (n ≡ 0 mod 12, n-1 prime, (n-2)/2 prime) remains formally OPEN
  as it requires showing that certain tuples of linear forms cannot all simultaneously
  be prime — a question related to Dickson's conjecture and covering congruences.
-/

open Finset in
/-- Even numbers ≥ 6 have at least 4 divisors: 1, 2, n/2, n. -/
lemma even_ge_six_divisors_ge_four (m : ℕ) (hm : 6 ≤ m) (heven : 2 ∣ m) :
    4 ≤ (Nat.divisors m).card := by
  have h_even_divisors : Nat.divisors m ⊇ {1, 2, m / 2, m} := by
    intro x; aesop
  exact le_trans (by rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem] <;> norm_num <;> omega) (Finset.card_mono h_even_divisors)

/-- For odd n > 24, the witness m = n-1 (even, ≥ 24) has m + τ(m) > n + 2. -/
lemma odd_case (n : ℕ) (hn : n > 24) (hodd : ¬ 2 ∣ n) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  use n - 1
  have h6 : 6 ≤ n - 1 := by omega
  have h_even : 2 ∣ (n - 1) := by omega
  constructor; · omega
  constructor; · omega
  have h_divisors_card : (n - 1).divisors.card ≥ 4 :=
    even_ge_six_divisors_ge_four _ h6 h_even
  omega

/-
PROBLEM
For n ≡ 2 mod 4 with n > 24: m = n-2 is divisible by 4 with (n-2)/4 ≥ 6,
    giving τ(n-2) ≥ 6.

PROVIDED SOLUTION
Use m = n-2. n-2 ≡ 0 mod 4 and n-2 ≥ 22. Write n-2 = 4k with k ≥ 6. The divisors of 4k include {1, 2, 4, k, 2k, 4k} which are 6 distinct elements since k ≥ 6 > 4. So τ(n-2) ≥ 6 and (n-2) + 6 = n + 4 > n + 2.
-/
lemma two_mod_four_case (n : ℕ) (hn : n > 24) (hmod : n % 4 = 2) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  -- Use m = n-2. n-2 ≡ 0 mod 4 and n-2 ≥ 22. Write n-2 = 4k with k ≥ 6. The divisors of 4k include {1, 2, 4, k, 2k, 4k} which are 6 distinct elements since k ≥ 6 > 4. So τ(n-2) ≥ 6.
  have h_divisors : ∀ k : ℕ, 6 ≤ k → (Nat.divisors (4 * k)).card ≥ 6 := by
    -- Let's choose any $k \geq 6$. We need to show that $4k$ has at least 6 divisors.
    intro k hk
    have h_divisors : Nat.divisors (4 * k) ≥ {1, 2, 4, k, 2 * k, 4 * k} := by
      simp +decide [ Finset.insert_subset_iff ];
      exact ⟨ by linarith, ⟨ ⟨ 2 * k, by ring ⟩, by linarith ⟩, by linarith, ⟨ 2, by ring ⟩, by linarith ⟩;
    exact le_trans ( by rcases k with ( _ | _ | _ | _ | _ | _ | k ) <;> simp +arith +decide at * ) ( Finset.card_mono h_divisors );
  use 4 * (n / 4);
  grind

/-
PROBLEM
Multiples of 12 ≥ 24 have at least 8 divisors.

PROVIDED SOLUTION
For j ≥ 2, 12j has at least divisors {1, 2, 3, 4, 6, 12, j, 12j}. Case split: for j = 2 through 12, verify computationally. For j ≥ 13 (j > 12), all 8 elements are distinct since j > 12 ≥ all the fixed elements, so τ(12j) ≥ 8.
-/
lemma mult_12_ge_24_divisors (j : ℕ) (hj : j ≥ 2) :
    (Nat.divisors (12 * j)).card ≥ 8 := by
  -- The set {1, 2, 3, 4, 6, 12, j, 12j} is a subset of the divisors of 12j.
  have h_subset : {1, 2, 3, 4, 6, 12, j, 12 * j} ⊆ Nat.divisors (12 * j) := by
    simp +decide [ Finset.insert_subset_iff ];
    grind;
  by_cases hj_ge_13 : j ≥ 13;
  · exact le_trans ( by rcases j with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j ) <;> simp +arith +decide at * ) ( Finset.card_mono h_subset );
  · interval_cases j <;> native_decide

/-
PROBLEM
Multiples of 6k for k ≥ 5 have at least 8 divisors.

PROVIDED SOLUTION
For k ≥ 5, 6k has at least divisors {1, 2, 3, 6, k, 2k, 3k, 6k}. For k = 5,6: verify computationally (τ(30)=8, τ(36)=9). For k ≥ 7 coprime to 6: all 8 are distinct since k > 6. For k ≥ 7 not coprime to 6, still has ≥ 8 divisors by similar argument.
-/
lemma mult_6_ge_30_divisors (k : ℕ) (hk : k ≥ 5) :
    (Nat.divisors (6 * k)).card ≥ 8 := by
  -- For $k > 6$, we show that $6k$ has at least 8 divisors.
  by_cases h₂ : k > 6;
  · -- For $k > 6$, the divisors of $6k$ include at least $1, 2, 3, 6, k, 2k, 3k, 6k$, so the cardinality is at least 8.
    have h_divisors : Nat.divisors (6 * k) ⊇ {1, 2, 3, 6, k, 2 * k, 3 * k, 6 * k} := by
      simp +decide [ Finset.insert_subset_iff ];
      exact ⟨ by linarith, ⟨ dvd_mul_of_dvd_left ( by decide ) _, by linarith ⟩, ⟨ dvd_mul_of_dvd_left ( by decide ) _, by linarith ⟩, by linarith, ⟨ ⟨ 3, by ring ⟩, by linarith ⟩, ⟨ ⟨ 2, by ring ⟩, by linarith ⟩ ⟩;
    refine' le_trans _ ( Finset.card_mono h_divisors );
    rcases k with ( _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.mul_succ ];
  · interval_cases k <;> native_decide

/-
PROBLEM
For n ≡ 0 mod 4, n > 24, n-1 composite:
    since n-1 ≡ 3 mod 4, n-1 can't be p², so τ(n-1) ≥ 4.

PROVIDED SOLUTION
Use m = n-1. Since n ≡ 0 mod 4, n-1 ≡ 3 mod 4. A perfect square p² is ≡ 0 or 1 mod 4, so n-1 ≠ p². Since n-1 is composite and not a prime square, there exists d with 1 < d < n-1 and d | (n-1) and (n-1)/d ≠ d. So {1, d, (n-1)/d, n-1} are 4 distinct divisors, τ(n-1) ≥ 4, and (n-1) + 4 = n+3 > n+2.
-/
lemma zero_mod_four_composite_case (n : ℕ) (hn : n > 24) (hmod : n % 4 = 0)
    (hcomp : ¬ Nat.Prime (n - 1)) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  use n - 1; rcases n with ( _ | _ | n ) <;> simp_all +arith +decide;
  -- Since $n+1$ is composite and greater than 4, it has at least 4 divisors.
  have h_divisors : ∃ d, 1 < d ∧ d < n + 1 ∧ d ∣ (n + 1) ∧ (n + 1) / d ≠ d := by
    by_contra h_contra;
    -- If no such $d$ exists, then $n+1$ must be a perfect square.
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = k ^ 2 := by
      obtain ⟨ k, hk ⟩ := Nat.exists_dvd_of_not_prime2 ( by linarith ) hcomp;
      exact ⟨ k, by nlinarith [ Nat.div_mul_cancel hk.1, show ( n + 1 ) / k = k from Classical.not_not.1 fun h => h_contra ⟨ k, hk.2.1, hk.2.2, hk.1, h ⟩ ] ⟩;
    rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num at * <;> omega;
  obtain ⟨ d, hd₁, hd₂, hd₃, hd₄ ⟩ := h_divisors; have h_divisors_set : Nat.divisors (n + 1) ⊇ {1, d, (n + 1) / d, n + 1} := by
    simp +decide [ Finset.insert_subset_iff ];
    exact ⟨ hd₃, Nat.div_dvd_of_dvd hd₃ ⟩;
  refine' le_trans _ ( Finset.card_mono h_divisors_set );
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num [ hd₁.ne', hd₂.ne, hd₄ ];
  · nlinarith [ Nat.div_mul_cancel hd₃ ];
  · exact id (Ne.symm hd₄);
  · exact ⟨ by linarith, by nlinarith [ Nat.div_mul_cancel hd₃ ], by linarith ⟩

/-
PROBLEM
For n ≡ 4 mod 12, n > 24, n-1 prime: m = n-4 is divisible by 12.

PROVIDED SOLUTION
Use m = n-4. Since n ≡ 4 mod 12, n-4 ≡ 0 mod 12. Write n-4 = 12j with j ≥ 2. By mult_12_ge_24_divisors, τ(12j) ≥ 8. So (n-4) + 8 = n+4 > n+2.
-/
lemma four_mod_twelve_prime_case (n : ℕ) (hn : n > 24) (hmod12 : n % 12 = 4)
    (hprime : Nat.Prime (n - 1)) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  -- Let $m = n - 4$. Since $n \equiv 4 \pmod{12}$, we have $n - 4 \equiv 0 \pmod{12}$, so $m$ is divisible by 12.
  set m := n - 4
  have hm_div : 12 ∣ m := by
    omega;
  obtain ⟨ k, hk ⟩ := hm_div;
  -- By Lemma 2, since $k \geq 2$, we have $\tau(12k) \geq 8$.
  have h_tau_ge_8 : (Nat.divisors (12 * k)).card ≥ 8 := by
    exact mult_12_ge_24_divisors k ( by omega );
  grind +ring

/-
PROBLEM
For n ≡ 8 mod 12, n > 24, n-1 prime: m = n-2 is divisible by 6.

PROVIDED SOLUTION
Use m = n-2. Since n ≡ 8 mod 12, n-2 ≡ 6 mod 12, so 6 | (n-2). Write n-2 = 6k with k ≥ 5. By mult_6_ge_30_divisors, τ(6k) ≥ 8. So (n-2) + 8 = n+6 > n+2.
-/
lemma eight_mod_twelve_prime_case (n : ℕ) (hn : n > 24) (hmod12 : n % 12 = 8)
    (hprime : Nat.Prime (n - 1)) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  -- Use m = n-2. Since n ≡ 8 mod 12, n-2 ≡ 6 mod 12, so 6 | (n-2). Write n-2 = 6k with k ≥ 5.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n - 2 = 6 * k ∧ 5 ≤ k := by
    exact ⟨ ( n - 2 ) / 6, by omega, by omega ⟩;
  -- By mult_6_ge_30_divisors, τ(6k) ≥ 8.
  have h_divisors : (Nat.divisors (6 * k)).card ≥ 8 := by
    exact mult_6_ge_30_divisors k hk.2;
  grind

/-
PROBLEM
For n ≡ 0 mod 12, n > 24, n-1 prime, with (n-2)/2 composite:
    m = n-2 has τ(n-2) ≥ 6.

PROVIDED SOLUTION
Use m = n - 2. n-2 is even, n-2 = 2 * ((n-2)/2). Since (n-2)/2 is composite (not prime) and (n-2)/2 ≥ 11, it has at least 3 divisors (it's not 1 and not prime). Actually since (n-2)/2 is odd and composite and ≥ 9, τ((n-2)/2) ≥ 3. Since (n-2)/2 is odd and coprime to 2: τ(n-2) = τ(2) · τ((n-2)/2) = 2 · τ((n-2)/2) ≥ 6. Then (n-2) + 6 = n + 4 > n + 2.

More precisely: (n-2)/2 is composite (not prime) and ≥ 11 (since n ≥ 36, n-2 ≥ 34, (n-2)/2 ≥ 17). Since it's composite, there exists d with 1 < d < (n-2)/2 and d | (n-2)/2. Then the divisors of n-2 include {1, 2, d, 2d, (n-2)/(2d), (n-2)/d, (n-2)/2, n-2}. Wait, simpler: n-2 = 2q where q = (n-2)/2 is composite odd. q has divisors 1, a, b, q (where a·b = q, a > 1, b > 1). Then n-2 = 2q has divisors 1, 2, a, 2a, b, 2b, q, 2q, and possibly more if a or b has further factors. At minimum, if q = a·b with a > 1: divisors include {1, 2, a, 2a, q/a, 2q/a} which are 6 distinct for a ≥ 3. For a = 2... but q is odd, so a ≥ 3.

Actually, the simplest approach: q is odd and ≥ 9 and not prime. So q has at least 4 divisors (1, p, q/p, q for some prime p | q; if q = p², these are 1, p, p² = 3 divisors, but then τ(2p²) = 2·3 = 6). So τ(n-2) = 2·τ(q) ≥ 2·3 = 6 when q = p², and ≥ 2·4 = 8 when q is not a prime power.
-/
lemma zero_mod_twelve_non_sophie_germain (n : ℕ) (hn : n > 24) (hmod12 : n % 12 = 0)
    (hprime : Nat.Prime (n - 1)) (hcomp2 : ¬ Nat.Prime ((n - 2) / 2)) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  by_cases h_n_minus_2_lt_50 : n < 50;
  · interval_cases n <;> simp_all +decide;
  · -- Since $n$ is a multiple of 12 and $n \geq 50$, we have $n - 2$ is divisible by 2 but not by 4. Thus, $n - 2 = 2q$ where $q$ is odd and composite.
    obtain ⟨q, hq⟩ : ∃ q, n - 2 = 2 * q ∧ Odd q ∧ ¬Nat.Prime q := by
      exact ⟨ ( n - 2 ) / 2, by rw [ Nat.mul_div_cancel' ( show 2 ∣ n - 2 from Nat.dvd_of_mod_eq_zero ( by omega ) ) ], by rw [ Nat.odd_iff ] ; omega, hcomp2 ⟩;
    -- Since $q$ is odd and composite, we have $\tau(q) \geq 3$.
    have h_tau_q_ge_3 : (Nat.divisors q).card ≥ 3 := by
      have h_tau_q_ge_3 : ∃ d, 1 < d ∧ d < q ∧ d ∣ q := by
        exact Exists.imp ( by tauto ) ( Nat.exists_dvd_of_not_prime2 ( by omega ) hq.2.2 );
      obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := h_tau_q_ge_3; exact Finset.two_lt_card.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩ ;
    -- Since $q$ is odd and composite, we have $\tau(2q) = 2 \cdot \tau(q)$.
    have h_tau_2q : (Nat.divisors (2 * q)).card = 2 * (Nat.divisors q).card := by
      have h_tau_2q : Nat.divisors (2 * q) = Nat.divisors q ∪ Finset.image (fun d => 2 * d) (Nat.divisors q) := by
        rw [ Nat.divisors_mul ];
        rw [ show Nat.divisors 2 = { 1, 2 } by rfl ] ; ext d; rw [ Finset.mem_mul ] ; aesop;
      rw [ h_tau_2q, Finset.card_union_of_disjoint ] <;> norm_num [ Finset.disjoint_right ];
      · rw [ two_mul, Finset.card_image_of_injective ] ; aesop_cat;
      · intros; subst_vars; exact absurd ( Nat.dvd_trans ( dvd_mul_right _ _ ) ‹_› ) ( by obtain ⟨ k, hk ⟩ := hq.2.1; aesop ) ;
    grind

/-- For n ≡ 0 mod 12, n > 24, n-1 prime, (n-2)/2 prime (Sophie Germain case):
    This is the hardest sub-case. The analysis involves Cunningham chains.

    STATUS: This sub-case is OPEN.

    When both (n-2)/2 and n-1 are prime (Sophie Germain pair), the witnesses n-1 and n-2
    each give m + τ(m) ≤ n + 2. One must look at n-3, n-4, n-5, or further.
    The chain of conditions for ALL nearby witnesses to fail simultaneously
    requires increasingly many numbers to be prime, which becomes impossible
    due to covering congruences — but a complete formal proof of this
    covering argument has not been achieved. -/
lemma zero_mod_twelve_sophie_germain (n : ℕ) (hn : n > 24) (hmod12 : n % 12 = 0)
    (hprime : Nat.Prime (n - 1)) (hprime2 : Nat.Prime ((n - 2) / 2)) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  sorry

/-- For n ≡ 0 mod 12, n > 24, n-1 prime. -/
lemma zero_mod_twelve_prime_case (n : ℕ) (hn : n > 24) (hmod12 : n % 12 = 0)
    (hprime : Nat.Prime (n - 1)) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  by_cases h : Nat.Prime ((n - 2) / 2)
  · exact zero_mod_twelve_sophie_germain n hn hmod12 hprime h
  · exact zero_mod_twelve_non_sophie_germain n hn hmod12 hprime h

/-- The main case for n ≡ 0 mod 4, combining all sub-cases. -/
lemma zero_mod_four_case (n : ℕ) (hn : n > 24) (hmod : n % 4 = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n + 2 < m + (Nat.divisors m).card := by
  by_cases hprime : Nat.Prime (n - 1)
  · by_cases h4 : n % 12 = 4
    · exact four_mod_twelve_prime_case n hn h4 hprime
    · by_cases h8 : n % 12 = 8
      · exact eight_mod_twelve_prime_case n hn h8 hprime
      · have h0 : n % 12 = 0 := by omega
        exact zero_mod_twelve_prime_case n hn h0 hprime
  · exact zero_mod_four_composite_case n hn hmod hprime

theorem erdos647 : ¬ ∃ n : ℕ, n > 24 ∧
    ∀ m : ℕ, 1 ≤ m → m < n → m + (Nat.divisors m).card ≤ n + 2 := by
  push_neg
  intro n hn
  by_cases hodd : ¬ 2 ∣ n
  · exact odd_case n hn hodd
  · push_neg at hodd
    by_cases h2 : n % 4 = 2
    · exact two_mod_four_case n hn h2
    · have h0 : n % 4 = 0 := by omega
      exact zero_mod_four_case n hn h0