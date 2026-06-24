/-
# Erdős Problem 267: Lacunary Fibonacci Reciprocal Irrationality

CLAIM: Let F_1 = F_2 = 1, F_{n+2} = F_{n+1} + F_n be the Fibonacci sequence.
Let n_1 < n_2 < n_3 < ... be a strictly increasing infinite sequence of positive
integers, and let c > 1 be a real constant such that n_{k+1} / n_k ≥ c for every k.
Then the series S = Σ_{k=0}^∞ 1 / F_{n_k} is irrational.

STATUS: OPEN for 1 < c < 2. Known for c ≥ 2 (Badea 1987).

This file proves the c ≥ 2 case using an irrationality criterion for series
with sufficiently fast-growing integer denominators (quadratic growth),
combined with a growth bound on Fibonacci numbers under index doubling.
-/
import Mathlib

open scoped BigOperators
open Nat Real

set_option maxHeartbeats 800000

/-! ## Part 1: Irrationality Criterion for Fast-Growing Reciprocal Sums

We prove that if (a_n) is a sequence of integers ≥ 2 satisfying
  a_{n+1} ≥ a_n²
for all n, then Σ 1/a_n is irrational.

The proof uses the "decreasing numerator" argument:
- The tail R_n = Σ_{k≥n} 1/a_k satisfies 1/a_n < R_n < 1/(a_n - 1)
- If R_n = p_n/q_n in lowest terms, then p_{n+1} < p_n
- A strictly decreasing sequence of positive integers cannot exist forever
-/

/-
Growth step: the one-step recurrence identity for the tail bound.
If a_{n+1} ≥ a_n² and a_n ≥ 2, then 1/a_n + 1/(a_{n+1}-1) < 1/(a_n-1).
-/
lemma growth_step_bound (an an1 : ℕ) (han : 2 ≤ an) (han1 : an ^ 2 ≤ an1) :
    (1 : ℝ) / an + 1 / ((an1 : ℝ) - 1) < 1 / ((an : ℝ) - 1) := by
  rw [ div_add_div, div_lt_div_iff₀ ] <;> nlinarith only [ show ( an : ℝ ) ≥ 2 by norm_cast, show ( an1 : ℝ ) ≥ an ^ 2 by norm_cast, sq ( an - 1 : ℝ ) ] ;

/-
Partial sum bound: Σ_{k=0}^{M} 1/a(n+k) < 1/(a(n)-1) for all n, M.
Proved by induction on M using the quadratic growth condition.
-/
lemma partial_sum_upper_bound
    (a : ℕ → ℕ)
    (ha_ge2 : ∀ n, 2 ≤ a n)
    (ha_growth : ∀ n, a n ^ 2 ≤ a (n + 1))
    (n M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), (1 : ℝ) / a (n + k) < 1 / ((a n : ℝ) - 1) := by
  induction' M with M ih generalizing n;
  · simpa using inv_strictAnti₀ ( by norm_num; linarith [ ha_ge2 n ] ) ( by linarith );
  · convert lt_trans _ ( growth_step_bound ( a n ) ( a ( n + 1 ) ) ( ha_ge2 n ) ( ha_growth n ) ) using 1;
    rw [ Finset.sum_range_succ' ];
    have := ih ( n + 1 ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;

/-
For a fast-growing sequence, the tail sum Σ_{k≥0} 1/a(n+k) is ≤ 1/(a(n) - 1).
-/
lemma tail_sum_le_bound
    (a : ℕ → ℕ)
    (ha_ge2 : ∀ n, 2 ≤ a n)
    (ha_growth : ∀ n, a n ^ 2 ≤ a (n + 1))
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (n : ℕ) :
    ∑' k, (1 : ℝ) / a (n + k) ≤ 1 / ((a n : ℝ) - 1) := by
  refine' le_of_tendsto_of_tendsto' ( Summable.hasSum ( by exact_mod_cast hsum.comp_injective ( add_right_injective n ) ) |> HasSum.tendsto_sum_nat ) tendsto_const_nhds fun M => _;
  convert le_trans _ ( le_of_lt ( partial_sum_upper_bound a ha_ge2 ha_growth n ( M - 1 ) ) ) using 1 ; cases M <;> norm_num [ Finset.sum_range_succ' ]

/-
For a fast-growing sequence, the tail sum Σ_{k≥0} 1/a(n+k) is strictly < 1/(a(n) - 1).
-/
lemma tail_sum_upper_bound
    (a : ℕ → ℕ)
    (ha_ge2 : ∀ n, 2 ≤ a n)
    (ha_growth : ∀ n, a n ^ 2 ≤ a (n + 1))
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (n : ℕ) :
    ∑' k, (1 : ℝ) / a (n + k) < 1 / ((a n : ℝ) - 1) := by
  -- From tail_sum_le_bound at n+1: tsum_{k≥0} 1/a(n+1+k) ≤ 1/(a(n+1)-1).
  have h_tail_bound_succ : (∑' (k : ℕ), (1 : ℝ) / (a (n + 1 + k))) ≤ 1 / ((a (n + 1) : ℝ) - 1) := by
    convert tail_sum_le_bound a ha_ge2 ha_growth hsum ( n + 1 ) using 1;
  rw [ ← Summable.sum_add_tsum_nat_add 1 ];
  · convert lt_of_le_of_lt ( add_le_add_left h_tail_bound_succ _ ) _ using 1 ; norm_num [ add_comm, add_left_comm, add_assoc ];
    convert rfl;
    convert growth_step_bound ( a n ) ( a ( n + 1 ) ) ( ha_ge2 n ) ( ha_growth n ) using 1 ; ring;
  · exact hsum.comp_injective ( add_right_injective n )

/-- For a sequence of positive terms, the tail sum is at least the first term. -/
lemma tail_sum_lower_bound
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (n : ℕ) :
    (1 : ℝ) / a n ≤ ∑' k, (1 : ℝ) / a (n + k) := by
  convert Summable.le_tsum (show Summable fun k => 1 / (a (n + k) : ℝ) from
    hsum.comp_injective (add_right_injective n)) 0 (fun _ _ => by positivity) using 1

/-- Key rational numerator decrease: if 0 < r < 1 is a rational number
and a ≥ 2 is a natural number with 1/a < r < 1/(a-1), then the
numerator (in lowest terms) of r - 1/a is strictly less than the
numerator of r. -/
lemma rat_num_decrease (r : ℚ) (a : ℕ) (ha : 2 ≤ a)
    (hr_pos : 0 < r) (hr_lt : r < 1)
    (hlb : 1 / (a : ℚ) < r) (hub : r < 1 / ((a : ℚ) - 1)) :
    (r - 1 / (a : ℚ)).num < r.num := by
  have h_pos : (a :) * r.num - r.den > 0 := by
    rw [Rat.lt_iff] at *; norm_num at *
    grind +splitIndPred
  have h_lt : (a :) * r.num - r.den < r.num := by
    have h_lt : r.num * (a - 1) < r.den := by
      rw [lt_div_iff₀] at hub <;> try norm_num; linarith
      rw [← Rat.num_div_den r] at hub; rw [div_mul_eq_mul_div, div_lt_iff₀] at hub <;>
        norm_cast at *; aesop
      exact r.pos
    lia
  have h_div : (r - 1 / (a : ℚ)).num ∣ (a : ℤ) * r.num - r.den := by
    rw [Rat.sub_def']
    simp +decide [Rat.mkRat_def]
    split_ifs <;> simp_all +decide [Rat.normalize]
    rw [Int.sign_eq_one_of_pos (by positivity)]; norm_num [mul_comm]
    exact Int.ediv_dvd_of_dvd <| Int.natCast_dvd.mpr <| Nat.gcd_dvd_left _ _
  exact lt_of_le_of_lt (Int.le_of_dvd (by linarith) h_div) h_lt

/-- The tail sums of a convergent series are summable. -/
lemma summable_tail (a : ℕ → ℕ)
    (hsum : Summable (fun n => (1 : ℝ) / a n)) (m : ℕ) :
    Summable (fun k => (1 : ℝ) / a (m + k)) :=
  hsum.comp_injective (add_right_injective m)

/-
The tail sum is strictly positive when all terms are positive.
-/
lemma tail_sum_pos
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (n : ℕ) :
    0 < ∑' k, (1 : ℝ) / a (n + k) := by
  refine' Summable.tsum_pos ..;
  exacts [ hsum.comp_injective ( add_right_injective n ), fun _ => div_nonneg zero_le_one ( Nat.cast_nonneg _ ), 0, div_pos zero_lt_one ( Nat.cast_pos.mpr ( ha_pos _ ) ) ]

/-
The tail sum is strictly less than 1 for a ≥ 2 with quadratic growth.
-/
lemma tail_sum_lt_one
    (a : ℕ → ℕ)
    (ha_ge2 : ∀ n, 2 ≤ a n)
    (ha_growth : ∀ n, a n ^ 2 ≤ a (n + 1))
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (n : ℕ) :
    ∑' k, (1 : ℝ) / a (n + k) < 1 := by
  by_cases hn : a n ≥ 3;
  · refine' lt_of_le_of_lt ( tail_sum_le_bound a ha_ge2 ha_growth hsum n ) _;
    rw [ div_lt_iff₀ ] <;> linarith [ show ( a n : ℝ ) ≥ 3 by norm_cast ];
  · -- Since $a(n �)� = 2$, we have $a(n+1) \geq 4$. Therefore, $\sum_{k=n+1}^{\infty} \frac{1}{a(k)} \leq \frac{1}{3}$.
    have h_tail_bound : ∑' k, (1 : ℝ) / a (n + 1 + k) ≤ 1 / 3 := by
      refine' le_trans ( tail_sum_le_bound _ _ _ _ _ ) _;
      · assumption;
      · assumption;
      · exact hsum;
      · exact one_div_le_one_div_of_le ( by norm_num ) ( by linarith [ show ( a ( n + 1 ) : ℝ ) ≥ 4 by exact_mod_cast by nlinarith [ ha_ge2 n, ha_growth n ] ] );
    rw [ Summable.tsum_eq_zero_add ];
    · norm_num [ add_comm, add_left_comm, add_assoc ] at *;
      interval_cases _ : a n <;> norm_num at * ; linarith;
      · linarith [ ha_ge2 n ];
      · linarith;
    · exact hsum.comp_injective ( add_right_injective n )

/-- The full sum is strictly less than 1/(a(0) - 1). -/
lemma sum_lt_bound
    (a : ℕ → ℕ)
    (ha_ge2 : ∀ n, 2 ≤ a n)
    (ha_growth : ∀ n, a n ^ 2 ≤ a (n + 1))
    (hsum : Summable (fun n => (1 : ℝ) / a n)) :
    ∑' n, (1 : ℝ) / a n < 1 / ((a 0 : ℝ) - 1) := by
  have := tail_sum_upper_bound a ha_ge2 ha_growth hsum 0
  simp at this ⊢
  exact this

/-
Irrationality criterion: If (a_n) is a sequence of integers ≥ 2 with
a_{n+1} ≥ a_n² for all n, and the series converges, then the sum is irrational.

The proof uses the decreasing numerator argument: if S = p/q, then the tail
R_n is a positive rational < 1 with 1/a_n < R_n < 1/(a_n - 1), and
(R_n - 1/a_n).num < R_n.num. Since numerators are positive integers,
this cannot decrease forever.
-/
theorem irrational_of_quadratic_growth_reciprocal_sum
    (a : ℕ → ℕ)
    (ha_ge2 : ∀ n, 2 ≤ a n)
    (ha_growth : ∀ n, a n ^ 2 ≤ a (n + 1))
    (hsum : Summable (fun n => (1 : ℝ) / a n)) :
    Irrational (∑' n, (1 : ℝ) / a n) := by
  intro h_rat
  obtain ⟨q, hq⟩ := h_rat
  set t : ℕ → ℚ := fun n => q - ∑ k ∈ Finset.range n, (1 : ℚ) / a k
  have ht_eq : ∀ n, t n = ∑' k, (1 : ℝ) / a (n + k) := by
    intro n
    simp [t, hq];
    rw [ ← Summable.sum_add_tsum_nat_add n ];
    · simp +decide [ add_comm n ];
    · simpa using hsum;
  -- Show that $t_n$ satisfies the hypotheses of `rat_num_decrease`.
  have ht_bounds : ∀ n, 0 < t n ∧ t n < 1 ∧ 1 / (a n :) < t n ∧ t n < 1 / ((a n : ℚ) - 1) := by
    intro n
    have ht_pos : 0 < t n := by
      exact_mod_cast ht_eq n |>.symm ▸ tail_sum_pos a ( fun n => by linarith [ ha_ge2 n ] ) hsum n
    have ht_lt_one : t n < 1 := by
      exact_mod_cast ht_eq n |>.symm ▸ tail_sum_lt_one a ha_ge2 ha_growth hsum n
    have ht_lower_bound : 1 / (a n :) < t n := by
      have ht_lower_bound : (1 : ℝ) / a n < t n := by
        rw [ ht_eq ];
        refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( Finset.range 2 ) ( fun _ _ => by positivity ) ( by simpa using summable_tail a hsum n ) ) ; norm_num [ Finset.sum_range_succ ];
        linarith [ ha_ge2 ( n + 1 ) ];
      rw [ div_lt_iff₀ ] at * <;> norm_cast at * ; linarith [ ha_ge2 n ];
      linarith [ ha_ge2 n ]
    have ht_upper_bound : t n < 1 / ((a n :) - 1) := by
      have := ht_eq n;
      convert tail_sum_upper_bound a ha_ge2 ha_growth hsum n using 1;
      rw [ ← this ] ; norm_cast
    exact ⟨ht_pos, ht_lt_one, ht_lower_bound, ht_upper_bound⟩;
  -- Apply `rat_num_decrease` to get the contradiction.
  have h_contradiction : ∀ n, (t (n + 1)).num < (t n).num := by
    intro n
    have ht_step : t (n + 1) = t n - 1 / (a n :) := by
      simp [t, Finset.sum_range_succ];
      ring;
    convert rat_num_decrease _ _ _ _ _ _ _ using 1 <;> aesop;
  -- Since $t_n$ is a rational number with a strictly decreasing numerator, this leads to a contradiction.
  have h_decreasing_num : StrictAnti (fun n => (t n).num) := by
    exact strictAnti_nat_of_succ_lt h_contradiction;
  exact absurd ( Set.infinite_range_of_injective h_decreasing_num.injective ) ( Set.not_infinite.mpr <| Set.Finite.subset ( Set.finite_Icc 0 <| ( t 0 |> Rat.num ) ) <| Set.range_subset_iff.mpr fun n => ⟨ Rat.num_nonneg.mpr <| le_of_lt <| ht_bounds n |>.1, h_decreasing_num.antitone n.zero_le ⟩ )

/-! ## Part 2: Fibonacci Growth Under Index Doubling -/

/-
F_{2n} ≥ F_n² for n ≥ 1.
This provides the quadratic growth condition needed for the irrationality criterion
when the index subsequence satisfies n_{k+1} ≥ 2 * n_k.
-/
lemma fib_sq_le_fib_double (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib n ^ 2 ≤ Nat.fib (2 * n) := by
  rw [ Nat.fib_two_mul ];
  nlinarith [ Nat.sub_add_cancel ( show fib n ≤ 2 * fib ( n + 1 ) from by linarith [ Nat.fib_mono ( Nat.le_succ n ) ] ), Nat.fib_mono ( Nat.le_succ n ) ]

/-- For m ≥ 2n with n ≥ 1, F_m ≥ F_n² -/
lemma fib_sq_le_fib_of_double_index {m n : ℕ} (hn : 1 ≤ n) (hm : 2 * n ≤ m) :
    Nat.fib n ^ 2 ≤ Nat.fib m :=
  le_trans (fib_sq_le_fib_double n hn) (Nat.fib_mono hm)

/-- For n ≥ 3, F_n ≥ 2 -/
lemma fib_ge_two {n : ℕ} (hn : 3 ≤ n) : 2 ≤ Nat.fib n :=
  Nat.le_trans (by decide) (Nat.fib_mono hn)

/-! ## Part 3: Summability of Fibonacci reciprocals -/

/-
The Fibonacci reciprocal series along any strictly increasing subsequence
is summable (since F_n grows exponentially).
-/
lemma summable_fib_reciprocal_subseq
    (n : ℕ → ℕ)
    (hn_pos : ∀ k, 0 < n k)
    (hn_strict : StrictMono n) :
    Summable (fun k => (1 : ℝ) / Nat.fib (n k)) := by
  -- By induction, we can show that $F_n \geq \left(\frac{3}{2}\right)^{n-2}$ for $n \geq 3$.
  have h_fib_lower_bound : ∀ n ≥ 3, Nat.fib n ≥ (3 / 2 : ℝ) ^ (n - 2) := by
    intro n hn; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | _ | n ) <;> norm_num [ Nat.fib_add_two ] at *;
    rcases n with ( _ | _ | n ) <;> norm_num [ Nat.fib_add_two, pow_succ' ] at *;
    have := ih ( n + 3 ) ( by linarith ) ( by linarith ) ; have := ih ( n + 4 ) ( by linarith ) ( by linarith ) ; norm_num [ Nat.fib_add_two, pow_succ' ] at *;
    norm_num [ Nat.succ_sub ] at * ; ring_nf at * ; linarith;
  -- Since $n$ is strictly monotone, $n(k) \geq k + n(0)$, so $F(n(k)) \geq \left(\frac{3}{2}\right)^{n(k) - 2}$.
  have h_fib_lower_bound_k : ∀ k, Nat.fib (n k) ≥ (3 / 2 : ℝ) ^ (n k - 2) := by
    intro k;
    by_cases hk : n k ≥ 3;
    · exact h_fib_lower_bound _ hk;
    · interval_cases _ : n k <;> norm_num;
      linarith [ hn_pos k ];
  -- Since $n$ is strictly monotone, $n(k) \geq k$, so we can bound the series by a geometric series.
  have h_geo_series : ∀ k, (1 : ℝ) / Nat.fib (n k) ≤ (1 : ℝ) / (3 / 2) ^ (k - 2) := by
    exact fun k => one_div_le_one_div_of_le ( by positivity ) ( le_trans ( pow_le_pow_right₀ ( by norm_num ) ( Nat.sub_le_sub_right ( hn_strict.id_le _ ) _ ) ) ( h_fib_lower_bound_k _ ) );
  exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => h_geo_series k ) ( summable_nat_add_iff 2 |>.1 <| by simpa using summable_geometric_of_lt_one ( by norm_num ) ( inv_lt_one_of_one_lt₀ <| by norm_num ) )

/-! ## Part 4: Erdős 267 — The c ≥ 2 Case -/

/-
Erdős 267 for c ≥ 2: When the lacunarity ratio is at least 2,
the Fibonacci reciprocal sum is irrational. This follows from the
irrationality criterion applied with a_k = F_{n_k}, using the
Fibonacci doubling growth bound F_{2n} ≥ F_n².
-/
theorem erdos267_c_ge_2
    (n : ℕ → ℕ)
    (hn_pos : ∀ k, 0 < n k)
    (hn_strict : StrictMono n)
    (hlac : ∀ k, 2 * n k ≤ n (k + 1))
    (hn_ge3 : ∀ k, 3 ≤ n k) :
    Irrational (∑' k, (1 : ℝ) / Nat.fib (n k)) := by
  convert irrational_of_quadratic_growth_reciprocal_sum ( fun k => Nat.fib ( n k ) ) ( fun k => fib_ge_two ( hn_ge3 k ) ) ( fun k => fib_sq_le_fib_of_double_index ( hn_pos k ) ( hlac k ) ) _ using 1;
  convert summable_fib_reciprocal_subseq n hn_pos hn_strict using 1

/-! ## Part 5: Full Conjecture (Open for 1 < c < 2) -/

/-- **Erdős Problem 267 (Full Conjecture):** For any lacunary subsequence
of Fibonacci reciprocals (with ratio ≥ c > 1), the sum is irrational.

STATUS: This remains OPEN for 1 < c < 2. The theorem `erdos267_c_ge_2`
above handles the case c ≥ 2, which was first proved by Badea (1987). -/
theorem erdos267
    (n : ℕ → ℕ)
    (hn_pos : ∀ k, 0 < n k)
    (hn_strict : StrictMono n)
    (c : ℝ)
    (hc : 1 < c)
    (hlac : ∀ k, c * (n k : ℝ) ≤ (n (k + 1) : ℝ)) :
    Irrational (∑' k, (1 : ℝ) / Nat.fib (n k)) := by
  sorry