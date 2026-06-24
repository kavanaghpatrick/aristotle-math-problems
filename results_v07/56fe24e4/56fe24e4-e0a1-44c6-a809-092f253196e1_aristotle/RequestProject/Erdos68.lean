import Mathlib

open scoped Nat BigOperators
open Finset Filter Real

noncomputable section

/-!
# Erdős Problem 68

**Statement**: Is the sum ∑_{n=2}^∞ 1/(n!-1) irrational?

**Status**: OPEN. This problem was posed by Erdős and remains unresolved.

## Key observations

1. The series converges (by comparison with ∑ 1/n!).
2. Using the geometric series identity 1/(n!-1) = ∑_{k≥1} 1/(n!)^k,
   the sum decomposes as S = (e-2) + R where R = ∑_{n≥2} 1/(n!(n!-1)).
3. The standard irrationality proof for e (multiply by N! and show the
   fractional part is strictly between 0 and 1) fails here because
   n!-1 does not divide N! in general — the prime factors of n!-1
   can be much larger than n (e.g., 6!-1 = 719 is prime).
4. The Liouville number approach also fails because the denominators
   of partial sums grow faster than the quality of approximation.

## What is proved below

- Convergence of the series (`summable_one_div_factorial_sub_one`)
- Algebraic decomposition of each term (`decompose_term`)
- Convergence of the remainder series (`summable_remainder`)
- The classical identity ∑ 1/n! = e (`sum_inv_factorial_eq_exp`)
- The identity ∑_{n≥2} 1/n! = e-2 (`sum_inv_factorial_from_two`)
- The decomposition S = (e-2) + R (`sum_decomposition`)

The main irrationality statement remains `sorry`.
-/

/-- The series ∑ 1/(n!-1) for n ≥ 2 is summable. -/
lemma summable_one_div_factorial_sub_one :
    Summable (fun n : ℕ => 1 / ((n + 2).factorial - 1 : ℝ)) := by
  have h_comp : ∀ n ≥ 2, (1 : ℝ) / ((Nat.factorial n) - 1) ≤ 2 / (Nat.factorial n) := by
    intro n hn
    rw [div_le_div_iff₀] <;>
      nlinarith [show (n ! : ℝ) ≥ 2 by
        exact_mod_cast Nat.le_trans (by decide) (Nat.factorial_le hn)]
  exact Summable.of_nonneg_of_le
    (fun n => div_nonneg zero_le_one <| sub_nonneg.2 <| mod_cast Nat.factorial_pos _)
    (fun n => h_comp _ <| by linarith)
    <| Summable.mul_left _ <| by
      simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_pow_div_factorial 1

/-- Each term 1/(n!-1) can be decomposed as 1/n! + 1/(n!(n!-1)) -/
lemma decompose_term (n : ℕ) :
    1 / ((n + 2).factorial - 1 : ℝ) =
    1 / (n + 2).factorial + 1 / ((n + 2).factorial * ((n + 2).factorial - 1)) := by
  field_simp
  rw [one_add_div] <;> norm_num
  linarith [show ((n + 2) ! : ℝ) > 1 from
    mod_cast Nat.lt_of_lt_of_le (by decide) (Nat.factorial_le (Nat.le_add_left _ _))]

/-- The "remainder" series ∑ 1/(n!(n!-1)) is summable -/
lemma summable_remainder :
    Summable (fun n : ℕ => 1 / ((n + 2).factorial * ((n + 2).factorial - 1) : ℝ)) := by
  have h_comparison : ∀ n : ℕ,
      1 / ((n + 2).factorial * ((n + 2).factorial - 1) : ℝ) ≤
      1 / ((n + 2).factorial - 1 : ℝ) := by
    intro n
    gcongr <;>
      nlinarith [show ((n + 2) ! : ℝ) ≥ 2 by
        exact_mod_cast Nat.le_trans (by decide) (Nat.factorial_le (Nat.le_add_left _ _))]
  exact Summable.of_nonneg_of_le
    (fun n => div_nonneg zero_le_one <|
      mul_nonneg (Nat.cast_nonneg _) <| sub_nonneg.2 <| mod_cast Nat.factorial_pos _)
    h_comparison <| by simpa using summable_one_div_factorial_sub_one

/-- The sum ∑_{n≥0} 1/n! equals e (Real.exp 1) -/
lemma sum_inv_factorial_eq_exp :
    ∑' n : ℕ, 1 / (n.factorial : ℝ) = exp 1 := by
  simp +decide [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum]

/-- ∑_{n≥2} 1/n! = e - 2 -/
lemma sum_inv_factorial_from_two :
    ∑' n : ℕ, 1 / ((n + 2).factorial : ℝ) = exp 1 - 2 := by
  convert HasSum.tsum_eq (hasSum_nat_add_iff' 2 |>.1 _) using 1 <;>
    norm_num [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum]
  · infer_instance
  · infer_instance
  · convert hasSum_nat_add_iff' 4 |>.2 <|
        Real.summable_pow_div_factorial 1 |> Summable.hasSum using 1
    norm_num
    norm_num [Finset.sum_range_succ, Nat.factorial]; ring

/-- The main sum decomposes as (e-2) + remainder -/
lemma sum_decomposition :
    ∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ) =
    (exp 1 - 2) + ∑' n : ℕ, 1 / ((n + 2).factorial * ((n + 2).factorial - 1) : ℝ) := by
  convert (tsum_congr fun n => decompose_term n) |> Eq.trans <| ?_ using 1
  rw [Summable.tsum_add, sum_inv_factorial_from_two]
  · simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_pow_div_factorial 1
  · exact summable_remainder

/-- Erdős Problem 68: The sum ∑_{n≥2} 1/(n!-1) is irrational.

This is an **open problem** in number theory. The standard approaches to proving
irrationality (multiplying by N! as in the proof for e, or Liouville-type
approximation arguments) do not directly apply because the denominators n!-1
lack the divisibility properties of n!.

The decomposition S = (e-2) + ∑ 1/(n!(n!-1)) shows that if the remainder
sum were rational, irrationality would follow from the irrationality of e.
However, proving the rationality (or irrationality) of the remainder sum
appears to be as difficult as the original problem. -/
theorem erdos_68 :
    Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) := by sorry
