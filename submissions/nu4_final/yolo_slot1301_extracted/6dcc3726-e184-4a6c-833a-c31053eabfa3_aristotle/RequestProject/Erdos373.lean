import Mathlib

open scoped Nat

namespace Erdos373

/-!
# Erdős Problem 373 (Surányi's Conjecture)

Surányi conjectured (1960s) that the equation `n! = a! · b!`
with `1 < b ≤ a` and `a + 1 ≠ n` has exactly one solution: `(n, a, b) = (10, 7, 6)`,
i.e. `10! = 7! · 6!`.

**Status**: OPEN since 1960s. Habsieger (2019, arXiv:1903.08370) verified
computationally up to very large bounds but no proof of full uniqueness exists.

## What we prove here

1. `factorial_10_eq` / `solution_10_7_6`: The triple (10, 7, 6) is a valid solution.
2. `n_gt_a`: If n! = a!·b! with b > 1, then n > a.
3. `n_ge_a_add_two`: Under the constraint a+1 ≠ n, we get n ≥ a+2.
4. `n_le_a_add_b`: The upper bound n ≤ a + b (from the binomial coefficient).
5. `erdos_373_suranyi`: The full conjecture (sorry — open problem).
-/

/-- 10! = 7! · 6! -/
theorem factorial_10_eq : (10 : ℕ).factorial = (7 : ℕ).factorial * (6 : ℕ).factorial := by
  native_decide

/-- (10, 7, 6) is a valid solution to n! = a!·b! with the given constraints. -/
theorem solution_10_7_6 :
    (10, 7, 6) ∈ {(n, a, b) : ℕ × ℕ × ℕ | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b
      ∧ b ≤ a ∧ a + 1 ≠ n} := by
  refine ⟨?_, by omega, by omega, by omega, by omega, by omega⟩
  native_decide

/-
If n! = a! * b! and b > 1, then n > a.
-/
theorem n_gt_a {n a b : ℕ} (heq : n ! = a ! * b !) (hb : 1 < b) : n > a := by
  contrapose! heq;
  exact ne_of_lt ( lt_of_le_of_lt ( Nat.factorial_le heq ) ( lt_mul_of_one_lt_right ( Nat.factorial_pos _ ) ( by linarith [ Nat.self_le_factorial b ] ) ) )

/-
Under the additional constraint a + 1 ≠ n, we get n ≥ a + 2.
-/
theorem n_ge_a_add_two {n a b : ℕ} (heq : n ! = a ! * b !) (hb : 1 < b)
    (hne : a + 1 ≠ n) : n ≥ a + 2 := by
  contrapose! hne; have := n_gt_a heq hb; linarith;

/-
n ≤ a + b, since (a+b)! ≥ a! * b! (the multinomial/binomial coefficient is ≥ 1).
-/
theorem n_le_a_add_b {n a b : ℕ} (heq : n ! = a ! * b !) (ha : 1 < a) : n ≤ a + b := by
  exact le_of_not_gt fun h => absurd heq.symm <| ne_of_lt <| by { exact lt_of_le_of_lt ( Nat.factorial_mul_factorial_dvd_factorial_add a b |> Nat.le_of_dvd ( by positivity ) ) <| by gcongr }

/-- **Erdős 373 / Surányi's Conjecture** (OPEN):
The only solution to `n! = a! · b!` with `1 < b ≤ a` and `a + 1 ≠ n`
is `(n, a, b) = (10, 7, 6)`.

This is an open problem in number theory, conjectured by Surányi in the 1960s.
No complete proof exists in the mathematical literature as of 2026. -/
theorem erdos_373_suranyi :
    {(n, a, b) : ℕ × ℕ × ℕ | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b
      ∧ b ≤ a ∧ a + 1 ≠ n} = {(10, 7, 6)} := by
  sorry

end Erdos373