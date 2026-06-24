import Mathlib

/-!
# Erdős Problem 267 — Fibonacci Subsequence Irrationality

**Status**: OPEN for 1 < c < 2. Proved for c ≥ 2 (Badea, 1987).

## Problem Statement

Let F_n be the Fibonacci numbers. If (n_k) is a strictly increasing
sequence of positive integers with n_{k+1}/n_k → c where 1 < c < 2,
is ∑ 1/F_{n_k} necessarily irrational?

## Known Results

- **c ≥ 2 (Badea 1987)**: The identity F_{2n} = F_n · L_n (where L_n is the
  Lucas sequence) implies F_{2n} > F_n² - F_n + 1, so the denominators grow
  at least quadratically. The Oppenheim/Brun irrationality criterion then gives
  irrationality of the sum.

- **c = 2 specifically**: ∑ 1/F_{2^k} is known to be transcendental
  (Duverney–Nishioka–Nishioka–Shiokawa, 1998, via Mahler's method).

## Why 1 < c < 2 is hard

For 1 < c < 2, F_{n_{k+1}} ≈ φ^{c · n_k} while F_{n_k}² ≈ φ^{2n_k}.
Since c < 2, we have c · n_k < 2n_k eventually, so
F_{n_{k+1}} / F_{n_k}² → 0, and the Oppenheim/Brun criterion
(which requires a_{k+1} ≥ a_k² - a_k + 1) fails.

No alternative irrationality criterion is known to cover this regime,
and no rational-valued counterexample has been constructed.

## Attempted approaches

- **Mahler's method**: Works for very specific lacunary sequences (like n_k = d^k)
  but does not generalize to arbitrary sequences with ratio tending to c.
- **Continued fraction analysis**: The partial quotients of ∑ 1/F_{n_k} do not
  have known structure when 1 < c < 2.
- **Algebraic independence methods**: Nesterenko-type results require specific
  functional equations that the Fibonacci recurrence does not provide in this regime.

This theorem remains as `sorry` — it represents an open conjecture.
-/

open Filter Topology

/-- Erdős Problem 267 (open case): If (n_k) is strictly increasing with
n_{k+1}/n_k → c for 1 < c < 2, then ∑ 1/F_{n_k} is irrational.

**Status**: OPEN. This is a well-known open problem in number theory.
The case c ≥ 2 was resolved by Badea (1987) using the Oppenheim criterion,
but the subquadratic growth regime 1 < c < 2 remains unresolved.
No proof or counterexample is currently known. -/
theorem erdos267_fibonacci (n : ℕ → ℕ) (hn_inc : StrictMono n)
    (c : ℝ) (hc1 : 1 < c) (hc2 : c < 2)
    (hlim : Filter.Tendsto (fun k => (n (k+1) : ℝ) / n k)
      Filter.atTop (nhds c)) :
    Irrational (∑' k, (1 : ℝ) / Nat.fib (n k)) := by sorry
