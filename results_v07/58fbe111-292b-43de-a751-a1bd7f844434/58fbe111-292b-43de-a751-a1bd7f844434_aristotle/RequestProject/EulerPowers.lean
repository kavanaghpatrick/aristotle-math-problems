import Mathlib

/-!
# Euler's Sum of Powers Conjecture (k ≥ 6)

Euler conjectured (1769) that for k ≥ 3, the equation
  a₁^k + a₂^k + ... + a_{k-1}^k = b^k
has no solution in positive integers — i.e., it takes at least k
k-th powers to sum to a k-th power.

This was disproved for:
- k = 5 by Lander–Parkin (1966): 27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵
- k = 4 by Elkies (1988): 2682440⁴ + 15365639⁴ + 18796760⁴ = 20615673⁴

For k ≥ 6, no counterexample has been found and no proof is known.

## Status

**OPEN PROBLEM.** The statement below remains unproven as of 2025. No proof
technique is known that can handle the general case k ≥ 6.

Natural approaches that fail:
- **Size arguments**: Bounding the sum by (k−1)·(b−1)^k and comparing to b^k
  does not yield a contradiction for all b.
- **Local (p-adic) obstructions**: No modular argument is known that rules out
  solutions for all k ≥ 6.
- **Descent / Fermat-style**: Wiles's proof of Fermat's Last Theorem (k ≥ 3,
  two summands) relies on the modularity of elliptic curves and does not
  generalize to sums of more than two k-th powers.

## References

- L. Euler, "Coniectura circa summam potestatum" (1769)
- L.J. Lander, T.R. Parkin, "Counterexample to Euler's conjecture on sums
  of like powers", Bull. AMS 72 (1966)
- N. Elkies, "On A⁴ + B⁴ + C⁴ = D⁴", Math. Comp. 51 (1988)
-/

/-- Euler's Sum of Powers Conjecture for k ≥ 6: there is no solution to
a₁^k + a₂^k + ... + a_{k-1}^k = b^k in positive integers.

This is an **open problem** — no proof or counterexample is known for k ≥ 6. -/
theorem euler_powers_k6 (k : ℕ) (hk : k ≥ 6) (a : Fin (k-1) → ℕ)
    (ha : ∀ i, a i > 0) (b : ℕ) (hb : b > 0) :
    ∑ i, (a i)^k ≠ b^k := by
  sorry
