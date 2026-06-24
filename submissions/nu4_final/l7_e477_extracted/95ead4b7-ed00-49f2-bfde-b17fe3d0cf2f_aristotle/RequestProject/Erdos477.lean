import Mathlib

open Polynomial Set

/-!
# Erdős Problem 477 — Cubic case (OPEN)

## Problem Statement

Erdős-Graham (after Sekanina 1959) asked: for which polynomials f ∈ ℤ[X] of degree ≥ 2
does there exist a set A ⊆ ℤ such that every integer z has a unique representation
z = a + f(n) with a ∈ A and n > 0?

## Known Results

- **Degree 2 (f = X²):** Sekanina [Sek59] proved NO — no such A exists. The key argument
  uses the growth rate of gaps between consecutive squares (linear growth, ~2n) combined
  with a counting/density analysis that forces contradictory arithmetic constraints.

- **Degree 3 (f = X³):** OPEN. This is the content of this file's main theorem.

## Why the Cubic Case is Hard

The cubic case resists known techniques for several reasons:

1. **No modular obstruction:** Cubes mod m = {0, 1, -1} for m = 7, 9, etc. These sets
   admit complementing sets in ℤ/mℤ for all tested moduli, so purely modular arguments
   cannot yield a contradiction.

2. **Density arguments are insufficient:** If such A existed, its counting function would
   satisfy |A ∩ [0, N]| ~ c·N^{2/3} where c = 9√3/(4π) ≈ 1.240. This asymptotic
   density is consistent with the integral constraints, unlike the square case where
   tighter arithmetic forces contradictions.

3. **Slower gap growth:** Consecutive cubes differ by 3n² + 3n + 1 (quadratic growth),
   compared to 2n + 1 (linear) for squares. The faster-growing gaps give cubes more
   "room" for a complementing set, making contradiction harder to derive.

## References

- Erdős, P., and Graham, R. L. "Old and New Problems and Results in Combinatorial
  Number Theory." L'Enseignement Mathématique, 1980. Problem 477.
- Sekanina, M. "On an ordered set of a decomposition of the set of natural numbers
  into classes." (Czech.) Čas. pro pěst. mat., 84 (1959), 319-321.
- erdosproblems.com/477
-/

/--
Erdős Problem 477 (Sekanina, cubic case):
There is no set A ⊆ ℤ such that every integer z has a unique representation
z = a + n³ with a ∈ A and n a positive integer.

**Status: OPEN.** Sekanina (1959) proved the quadratic case (f = X²).
The cubic case remains open as of 2026. Multiple automated proof attempts
(including density arguments, modular analysis, and counting methods)
have been unable to close this gap.
-/
theorem erdos_477_X_pow_three : letI f : ℤ[X] := X ^ 3
    ∀ A : Set ℤ, ∃ z : ℤ, ¬ ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry
