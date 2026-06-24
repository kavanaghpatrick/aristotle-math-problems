import Mathlib

open scoped Nat

namespace Erdos373

/-!
# Erdős Problem 373 — Surányi's Conjecture

Surányi conjectured (1960s) that the equation `n! = a! * b!`
with `1 < b ≤ a` and `a + 1 ≠ n` has exactly one solution:
`(n, a, b) = (10, 7, 6)`, i.e., `10! = 7! * 6! = 3628800`.

**Status**: OPEN since the 1960s. No proof exists in the literature.
Habsieger (2019, Fibonacci Q. 57(1), arXiv:1903.08370) verified the
conjecture computationally up to large bounds.

## Proved partial results (sorry-free)

We prove the following structural results about any solution:

- **`mem_solutions`**: `(10, 7, 6)` satisfies all constraints.
- **`bound_a_lt_n`**: Any solution satisfies `a < n`.
- **`bound_lower`**: Any solution satisfies `a + 2 ≤ n`.
- **`ascending_eq_factorial`**: Any solution satisfies `n! / a! = b!`.
- **`no_prime_in_interval`**: No prime exists in `(a, n]` for any solution.
- **`bound_upper`**: Any solution satisfies `n < 2 * a` (via Bertrand's postulate).

## What remains (sorry)

The main theorem `erdos_373_suranyi` equating `SolutionSet` with `{(10, 7, 6)}`
is left as `sorry`. The proved bounds reduce any solution to the "corridor"
`a + 2 ≤ n < 2a` with no prime in `(a, n]`, but closing the gap—showing that
the product `(a+1)(a+2)⋯n` is never a factorial `b!` with `b ≤ a` except for
`(n, a, b) = (10, 7, 6)`—would require bounding `a` from above, which is the
core open difficulty.
-/

/-- The solution set of Surányi's equation. -/
def SolutionSet : Set (ℕ × ℕ × ℕ) :=
  {(n, a, b) | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b ∧ b ≤ a ∧ a + 1 ≠ n}

/-- Verify that `(10, 7, 6)` satisfies all constraints. -/
theorem mem_solutions : (10, 7, 6) ∈ SolutionSet := by
  refine ⟨?_, by omega, by omega, by omega, by omega, by omega⟩
  native_decide

/-- Any solution satisfies `a < n`. -/
theorem bound_a_lt_n {n a b : ℕ} (h : (n, a, b) ∈ SolutionSet) : a < n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact not_le.mp fun h =>
    by nlinarith [Nat.self_le_factorial n, Nat.factorial_pos a,
      Nat.factorial_le h, Nat.self_le_factorial b, Nat.factorial_pos b]

/-- Any solution satisfies `a + 2 ≤ n` (since `a + 1 ≠ n` and `a < n`). -/
theorem bound_lower {n a b : ℕ} (h : (n, a, b) ∈ SolutionSet) : a + 2 ≤ n := by
  have := bound_a_lt_n h
  exact Nat.lt_of_le_of_ne this (by rintro rfl; exact h.2.2.2.2.2 (by linarith))

/-- The ascending factorial `(a+1)(a+2)⋯n` equals `b!` for any solution. -/
theorem ascending_eq_factorial {n a b : ℕ} (h : (n, a, b) ∈ SolutionSet) :
    n ! / a ! = b ! := by
  rw [Nat.div_eq_of_eq_mul_left] <;> nlinarith [h.1, Nat.factorial_pos a]

/-- Any prime in `(a, n]` would divide `b!` yet exceed `b`, a contradiction.
    Hence no prime exists in `(a, n]`. -/
theorem no_prime_in_interval {n a b : ℕ} (h : (n, a, b) ∈ SolutionSet)
    {p : ℕ} (hp : Nat.Prime p) (hpa : a < p) (hpn : p ≤ n) : False := by
  obtain ⟨heq, _, _, _, hba, _⟩ := h
  have h_div : p ∣ a ! ∨ p ∣ b ! := by
    exact hp.dvd_mul.mp (dvd_trans (Nat.dvd_factorial hp.pos hpn) (by aesop))
  exact absurd (h_div.resolve_right (by rw [Nat.Prime.dvd_factorial hp]; linarith))
    (by rw [Nat.Prime.dvd_factorial hp]; linarith)

/-- By Bertrand's postulate and the no-prime constraint, `n < 2 * a`. -/
theorem bound_upper {n a b : ℕ} (h : (n, a, b) ∈ SolutionSet) : n < 2 * a := by
  obtain ⟨p, hp_prime, hp_bounds⟩ : ∃ p, Nat.Prime p ∧ a < p ∧ p ≤ 2 * a := by
    exact Nat.exists_prime_lt_and_le_two_mul a (by linarith [h.2.2.1])
  exact lt_of_not_ge fun hn =>
    no_prime_in_interval h hp_prime hp_bounds.1 <| hp_bounds.2.trans hn

/--
**Surányi's Conjecture (Erdős Problem 373, OPEN since 1960s)**:
The equation `n! = a! * b!` with `1 < b ≤ a` and `a + 1 ≠ n`
has exactly one solution: `(n, a, b) = (10, 7, 6)`.

This is an open problem in number theory. The containment
`{(10, 7, 6)} ⊆ SolutionSet` is verified by `mem_solutions`; the reverse
inclusion (uniqueness) has no known proof in the mathematical literature.
-/
theorem erdos_373_suranyi :
    {(n, a, b) : ℕ × ℕ × ℕ | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b
      ∧ b ≤ a ∧ a + 1 ≠ n} = {(10, 7, 6)} := by
  sorry

end Erdos373
