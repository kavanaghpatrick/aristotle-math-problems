import Mathlib

/-!
# Erdős Problem 936: Finitely Many Powerful 2^n + 1

A number is *powerful* if every prime factor appears with exponent ≥ 2.

**Conjecture (Erdős):** There are only finitely many n ≥ 1 such that 2^n + 1 is powerful.

The only known powerful value is 2³ + 1 = 9 = 3².

**Status:** OPEN. Conditionally follows from the ABC conjecture.
No unconditional proof is known as of 2024.

## References

- Erdős, P. "Some of my favourite problems which recently have been solved."
- Guy, R. K. *Unsolved Problems in Number Theory*, Problem B16.
-/

/-- **Erdős Problem 936.** There are only finitely many `n ≥ 1` such that `2^n + 1` is powerful
(every prime divisor `p` satisfies `p² ∣ 2^n + 1`).

This is an **open problem**. The only known solution is `n = 3` (giving `9 = 3²`).
Finiteness follows conditionally from the ABC conjecture, but no unconditional proof is known. -/
theorem erdos936 : Set.Finite
    {n : ℕ | n ≥ 1 ∧
      ∀ p : ℕ, Nat.Prime p → p ∣ (2 ^ n + 1) → p ^ 2 ∣ (2 ^ n + 1)} := by
  sorry
