import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

/-!
# Erdős Problem 672 (k=4, l=3)

**Conjecture:** For any positive integers `n` and `d` with `gcd(n, d) = 1`, the product
`n(n+d)(n+2d)(n+3d)` is never a perfect cube.

## Status

This is an **open problem** in number theory. The theorem statement below remains unproved
(`sorry`). No known proof exists in the literature as of 2026.

## Analysis

### Key algebraic identity
The product satisfies the identity (verified in Lean below):
  `n(n+d)(n+2d)(n+3d) = (n² + 3nd + d²)² - d⁴`

So the equation `n(n+d)(n+2d)(n+3d) = m³` is equivalent to `T² - m³ = d⁴`
where `T = n² + 3nd + d²`. This is a family of Mordell-type equations parameterized by `d`.

### Factorization approach
Setting `A = n(n+3d)` and `B = (n+d)(n+2d)`, we have `AB = m³` with `B - A = 2d²`.
When `gcd(n,d) = 1`, the gcd of `A` and `B` divides `2`. This leads to:
- **Coprime case** (`n` odd, `d` even): `A = a³`, `B = b³`, and `(b-a)(b²+ab+a²) = 2d²`.
  The sub-case `b - a = 1` is ruled out by parity (yields `3a²+3a+1 = 2d²`, but the LHS
  is always odd). Further sub-cases reduce to Pell equations coupled with elliptic curves.
- **Even-gcd case** (both odd, or `n` even `d` odd): Similar descent with factor of 2.

Each sub-case ultimately requires showing that specific families of elliptic curves (genus ≥ 1)
have no integral points satisfying additional arithmetic constraints. While Faltings' theorem
guarantees finiteness for each fixed `d`, a uniform proof across all `d` remains open.

### Why the Vinogradov mean-value approach fails
The informal proof outline using Wooley's efficient congruencing / Bourgain-Demeter-Guth
decoupling is **not valid**: these results give upper bounds on solution counts
(`O(N^{1+ε})`), but the claimed "density contradiction" (that one solution generates
`≫ N^{1+δ}` shifted solutions) is not established. Translation invariance of Vinogradov
systems only gives `O(N)` shifted candidates from a single solution, which is consistent
with the `O(N^{1+ε})` upper bound.

### Computational verification
No solutions exist for `n, d ≤ 100` (verified computationally).
-/

/-- The key algebraic identity for products of 4-term arithmetic progressions. -/
theorem ap4_product_identity (n d : ℤ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 - d ^ 4 := by
  ring

/-- The difference between the two "middle" and "outer" pairings. -/
theorem ap4_pairing_diff (n d : ℤ) :
    (n + d) * (n + 2 * d) - n * (n + 3 * d) = 2 * d ^ 2 := by
  ring

/-- **Erdős Problem 672 (k=4, l=3)** — OPEN PROBLEM.
For any positive integers `n` and `d` with `gcd(n, d) = 1`, the product
`n(n+d)(n+2d)(n+3d)` is never a perfect cube. -/
theorem erdos_672_k4_l3 :
    ∀ n d : ℕ, n > 0 → d > 0 → n.gcd d = 1 →
    ¬ ∃ m : ℕ, (∏ i ∈ Finset.range 4, (n + i * d)) = m ^ 3 := by
  sorry
