import Mathlib

open Polynomial

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 477 — Cubic Case

## Statement

For the polynomial f(n) = n³, there is no set A ⊂ ℤ such that every integer z
has exactly one representation z = a + n³ with a ∈ A and n > 0.

## Status: OPEN

This is the cubic case of Erdős Problem 477 (1959). The quadratic case f(n) = n²
was resolved by Sekanina in 1959, and generalized by AlphaProof in January 2026
to a·n² + b·n + c with a | b, a and b nonzero. The cubic case remains open as of
May 2026 per erdosproblems.com/477 and the teorth/erdosproblems AI-contributions wiki.

## Why the modular approach fails for cubes

The proof strategy suggested (modular obstruction via cube residues mod 7, 9, 13, etc.)
does NOT yield a contradiction for the cubic case. Here is the Fourier-analytic reason:

For unique representation A + C = ℤ (where C = {n³ : n ≥ 1}), reducing mod m and
taking Fourier transforms on ℤ/mℤ, we need f̂_A(k) · ĝ_C(k) = 0 for all k ≠ 0.
If ĝ_C(k) ≠ 0 at every non-trivial character, then A must be uniform mod m
(which is consistent, not contradictory). If ĝ_C(k) = 0 at some k, A has freedom
at those frequencies (also not contradictory).

- **Mod 7:** Cube residues are {0, 1, 6} with multiplicities (1, 3, 3).
  ĝ(k) = 1 + 6·cos(2πk/7) ≠ 0 for k = 1,...,6.
  Forces A uniform mod 7. ✓ Consistent.

- **Mod 9:** Cube residues are {0, 1, 8} with equal multiplicity (3, 3, 3).
  ĝ(k) = 3(1 + 2·cos(2πk/9)), which vanishes at k = 3, 6.
  A must be uniform within residue classes mod 3. ✓ Consistent.

- **Mod 13:** Cube residues are {0, 1, 5, 8, 12} with multiplicities (1, 3, 3, 3, 3).
  ĝ(k) ≠ 0 for all k ≠ 0. Forces A uniform mod 13. ✓ Consistent.

No combination of moduli produces an inconsistency. Contrast with the X² case, where
the consecutive differences 2n+1 cover all odd numbers, enabling a density/counting
argument that has no cubic analogue.

## Verified preliminary results

We prove:
1. The cubic difference identity: (n+1)³ - n³ = 3n² + 3n + 1
2. Centered hexagonal numbers are ≡ 1 mod 6
3. Cube residues mod 7 are exactly {0, 1, 6}
-/

/-- Cubic difference identity: (n+1)³ - n³ = 3n² + 3n + 1 -/
theorem cube_difference (n : ℤ) : (n + 1) ^ 3 - n ^ 3 = 3 * n ^ 2 + 3 * n + 1 := by
  ring

/-
The centered hexagonal numbers 3n² + 3n + 1 are congruent to 1 mod 6 for all n ≥ 0
-/
theorem centered_hex_mod_6 (n : ℤ) : (3 * n ^ 2 + 3 * n + 1) % 6 = 1 := by
  norm_num [ sq, Int.add_emod, Int.mul_emod ] ; have := Int.emod_nonneg n ( by decide : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos n ( by decide : ( 6 : ℤ ) > 0 ) ; interval_cases n % 6 <;> trivial;

/-
Cubes mod 7 take values in {0, 1, 6}
-/
theorem cube_mod_7 (n : ℤ) : n ^ 3 % 7 = 0 ∨ n ^ 3 % 7 = 1 ∨ n ^ 3 % 7 = 6 := by
  norm_num [ pow_succ, Int.mul_emod ] ; have := Int.emod_nonneg n ( by decide : ( 7 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos n ( by decide : ( 7 : ℤ ) > 0 ) ; interval_cases n % 7 <;> trivial;

/-- **Erdős Problem 477 (cubic case) — OPEN PROBLEM**

No set A ⊂ ℤ is a unique-representation complement of {n³ : n > 0} in ℤ.
That is, for every A there exists z such that z does not have exactly one
representation z = a + n³ with a ∈ A and n > 0.

This remains an open problem as of May 2026. The `sorry` below reflects the
genuinely unresolved mathematical status of this conjecture.
-/
theorem erdos_477_x_pow_three : letI f : ℤ[X] := X ^ 3
    ∀ A : Set ℤ, ∃ z : ℤ, ¬ ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry