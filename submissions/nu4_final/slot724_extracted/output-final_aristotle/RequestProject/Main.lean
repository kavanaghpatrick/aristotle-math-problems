import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000

/--
# Erdős Problem 203

**Statement:** There exists a positive integer `m` coprime to 6 such that for every
`k, l ≥ 0`, the number `2^k * 3^l * m + 1` is composite (never prime).

**Status: OPEN.** This is an analogue of the Sierpiński/Riesel covering-system problem.
The variant without the `3^l` factor (i.e., `2^k * m + 1` composite for all `k`)
is solved via classical covering congruences. The `3^l` twist is unresolved.

## Analysis

The natural approach via covering congruences requires covering the 2D lattice ℤ²₊
of `(k, l)` pairs. For each prime `p > 3`:
- The subgroup `⟨2, 3⟩ ⊆ (ℤ/pℤ)*` determines the period lattice.
- Each prime covers a single coset of this lattice, a fraction `1/|⟨2,3⟩|` of all pairs.

Computational exploration shows that for all primes `p < 300`:
- For most primes, `⟨2, 3⟩ = (ℤ/pℤ)*` (index 1), so each covers `1/(p-1)`.
- Only primes `p ∈ {23, 47, 71, 73, 97, 167, 191, 193, 239, 241, 263, ...}` have
  index 2, and the maximum index found is always 2.

The 2D covering problem is substantially harder than the 1D case because different primes
impose conditions along different "directions" in the `(k, l)` lattice. A proof would
require either:
1. An explicit covering system with compatible modular conditions in 2 dimensions, or
2. A non-constructive existence argument (e.g., via density or algebraic methods).

Both approaches remain open as of 2026.
-/
theorem erdos_203_existence :
    ∃ m : ℕ, m > 0 ∧ m.Coprime 6 ∧
    ∀ k l : ℕ, ¬ (2^k * 3^l * m + 1).Prime := by sorry
