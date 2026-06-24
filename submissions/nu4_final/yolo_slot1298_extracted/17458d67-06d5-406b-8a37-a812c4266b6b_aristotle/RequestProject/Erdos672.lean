import Mathlib

/-!
# Erdős Problem 672: Four-term coprime AP product is never a cube

**Statement**: For all sufficiently large `n` there is no positive integer `d` coprime
to `n` with `d > 0` and no positive integer `m` such that the product
`n(n+d)(n+2d)(n+3d)` equals `m³`.

## Status

This is an **open problem** in number theory (Erdős Problem 672). Computational
verification up to `n, d ≤ 5000` finds no coprime solutions, strongly suggesting
that no solution exists for any `n ≥ 1`.

## Mathematical Analysis

### Key structural facts

When `gcd(n, d) = 1`:

1. **Coprimality of middle terms**: `gcd(n+d, n+2d) = gcd(n+d, d) = gcd(n, d) = 1`,
   so `n+d` and `n+2d` are always coprime.

2. **Prime factorization constraint**: For any prime `p ≥ 5`, `p` divides at most one
   of the four terms `n, n+d, n+2d, n+3d`. Therefore, `vₚ` of each individual factor
   must be divisible by 3 for the product to be a cube.

3. **Algebraic identity**: The product equals `(n²+3nd+d²)² - d⁴`, placing solutions
   on the Mordell-type curve `t² = m³ + d⁴`.

### Proof approach (partially formalized)

The proof splits into cases by the parities of `n` and `d` and the residues mod 3.

**Sub-case handled by FLT3** (`d` odd, `n` odd, `v₂(n+d) ≡ 2 mod 3`):
- Write `T = (n+d)/2` (even), `S = (n+3d)/2` (odd).
- The product equals `4nTS(n+2d)`.
- The quantities `n`, `T/2^{v₂(T)}`, `S`, and `n+2d` are pairwise coprime odd integers.
- Each must be a perfect cube: `n = a³`, `T/2^{v₂(T)} = b³`, `S = c³`, `n+2d = e³`.
- Algebraic manipulation gives `e³ + a³ = (2^{(v₂(n+d)+1)/3} · b)³`.
- This contradicts `fermatLastTheoremThree` (FLT for `n = 3`), which is proved in Mathlib.

**Sub-cases NOT handled by FLT3**:
- When `n` odd, `d` even, `gcd(n,3) = 1`: all four terms are pairwise coprime cubes,
  giving four cubes in arithmetic progression. Eliminating this requires the classical
  result that `a³ + c³ = 2b³` has no solution in positive integers with `a ≠ c`
  (proved by Euler via descent in `ℤ[ζ₃]`). **Not available in Mathlib.**

- When `d` odd, `n` odd, `v₂(n+d) = 1`: leads to `e³ + a³ = 4h³` which requires
  showing this Diophantine equation has no coprime positive integer solutions.
  This can be proved via mod 9 analysis (partial) and descent in `ℤ[ζ₃]` (full).
  **Not available in Mathlib.**

### What would be needed in Mathlib

To complete this proof, one would need to formalize one of:
- Euler's theorem that no three distinct positive cubes are in arithmetic progression
- Faltings' theorem (finiteness of rational points on curves of genus ≥ 2)
- The descent argument in `ℤ[ζ₃]` for equations `a³ + c³ = 2b³` and `a³ + c³ = 4b³`
-/

section HelperLemmas

/-! ### Proved structural lemmas -/

/-
The middle two terms of a coprime AP are coprime.
-/
lemma coprime_middle_terms (n d : ℕ) (h : n.gcd d = 1) :
    (n + d).gcd (n + 2 * d) = 1 := by
  simpa [ ( by ring : n + 2 * d = n + d + d ) ] using h

/-- The product identity: n(n+d)(n+2d)(n+3d) = (n²+3nd+d²)² - d⁴ over ℤ -/
lemma product_identity (n d : ℤ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) =
    (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 - d ^ 4 := by
  ring

/-- Product expansion: the Finset.range 4 product equals n(n+d)(n+2d)(n+3d). -/
lemma prod_range_four_eq (n d : ℕ) :
    (∏ i ∈ Finset.range 4, (n + i * d)) =
    n * (n + d) * (n + 2 * d) * (n + 3 * d) := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  ring

end HelperLemmas

/-! ### Main theorem -/

open Finset in
theorem erdos_672_k4_l3 :
    ∃ N0 : ℕ, ∀ n d : ℕ, n ≥ N0 → d > 0 → n.gcd d = 1 →
    ¬ ∃ m : ℕ, (∏ i ∈ Finset.range 4, (n + i * d)) = m ^ 3 := by
  sorry