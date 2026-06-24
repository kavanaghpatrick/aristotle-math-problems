import Mathlib

open scoped Nat

namespace Erdos373

/-!
# Erdős Problem 373 (Surányi's Conjecture)

Surányi conjectured (1960s, open since) that the equation `n! = a! · b!` with
`1 < b ≤ a`, `a + 1 ≠ n` has only the solution `(n, a, b) = (10, 7, 6)`,
i.e. `10! = 7! · 6!`.

**Status**: OPEN since 1960s. `(10, 7, 6)` is the only known non-trivial solution
and is conjectured unique. No known proof exists.
-/

/-- The known solution: 10! = 7! · 6! -/
theorem erdos_373_known_solution : (10 : ℕ).factorial = (7 : ℕ).factorial * (6 : ℕ).factorial := by
  rfl

/-
By Bertrand's postulate, any solution must satisfy `n < 2 * a`.
-/
theorem erdos_373_bound {n a b : ℕ} (hfact : n ! = a ! * b !)
    (ha : 1 < a) (hb : 1 < b) (hba : b ≤ a) (hne : a + 1 ≠ n) (_hn : 1 < n) :
    n < 2 * a := by
  contrapose! hfact;
  refine' ne_of_gt _;
  refine' lt_of_lt_of_le _ ( Nat.factorial_le hfact );
  induction ha <;> simp_all +decide [ Nat.factorial_succ, Nat.mul_succ ];
  · interval_cases b ; trivial;
  · rename_i k hk ih;
    rcases hba with ( _ | hba ) <;> simp_all +decide [ Nat.factorial_succ, mul_assoc ];
    · ring_nf;
      nlinarith only [ hk, show k ! ^ 2 ≤ ( k * 2 ) ! from by rw [ sq ] ; exact Nat.le_of_dvd ( Nat.factorial_pos _ ) ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by ring_nf; norm_num ), Nat.factorial_pos k ];
    · exact lt_of_le_of_lt ( Nat.mul_le_mul_left _ ( ih ( by linarith ) ( by linarith ) |> le_of_lt ) ) ( by nlinarith [ Nat.factorial_pos ( 2 * k ), Nat.factorial_succ ( 2 * k ) ] )

/-
For any solution, we have `a + 2 ≤ n`.
-/
theorem erdos_373_lower {n a b : ℕ} (hfact : n ! = a ! * b !)
    (_ha : 1 < a) (hb : 1 < b) (_hba : b ≤ a) (hne : a + 1 ≠ n) (_hn : 1 < n) :
    a + 2 ≤ n := by
  -- Since $a$ and $b$ are greater than 1, we have $n > a$.
  have h_gt_a : n > a := by
    contrapose! hfact;
    exact ne_of_lt ( lt_of_le_of_lt ( Nat.factorial_le hfact ) ( lt_mul_of_one_lt_right ( Nat.factorial_pos _ ) ( by linarith [ Nat.self_le_factorial b ] ) ) );
  omega

/-- Surányi's conjecture (Erdős Problem 373, OPEN):
The equation `n! = a! · b!` with `1 < b ≤ a`, `a + 1 ≠ n` has only the solution
`(n, a, b) = (10, 7, 6)`. -/
theorem erdos_373_suranyi :
    {(n, a, b) : ℕ × ℕ × ℕ | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b ∧ b ≤ a ∧ a + 1 ≠ n}
      = {(10, 7, 6)} := by
  sorry

end Erdos373