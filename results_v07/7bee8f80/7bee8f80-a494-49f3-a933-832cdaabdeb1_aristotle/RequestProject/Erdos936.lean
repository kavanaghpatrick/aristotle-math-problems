import Mathlib

/-!
# Erdős Problem 936

Is `2^n + 1` powerful for only finitely many `n`?

A natural number is *powerful* (also called *squarefull*) if every prime factor appears
with exponent ≥ 2 in its prime factorization.

## Status

**OPEN.** Expected answer: yes, `2^n + 1` is powerful for only finitely many `n`.
More precisely, the only known values are `n = 0` (giving `2^0 + 1 = 2`, which is
not powerful) and no `n` with `2^n + 1` powerful is known.

The problem is part of a family of four variants asking the same question for
`2^n ± 1` and `n! ± 1`.

Under the ABC conjecture, the result follows: if `2^n + 1` is powerful then
`rad(2^n + 1) ≤ (2^n + 1)^{1/2}`, and `rad(2 · 1 · (2^n + 1)) ≤ 2 · (2^n + 1)^{1/2}`,
which contradicts `rad(abc) ≥ c^{1-ε}` for `a + b = c` with `(a,b) = (1, 2^n)` when
`n` is large enough.
-/

open Filter

namespace Nat

/-- A natural number `n` is *powerful* (or *squarefull*) if every prime in its
factorization appears with exponent at least 2. Equivalently, for every prime `p`,
if `p ∣ n` then `p ^ 2 ∣ n`. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- **Erdős Problem 936.** For all sufficiently large `n`, `2^n + 1` is not powerful.
Equivalently, the set of `n` for which `2^n + 1` is powerful is finite.

This is an **open problem**. -/
theorem erdos_936 :
    ∀ᶠ n in atTop, ¬ (2 ^ n + 1 : ℕ).Powerful := by sorry

end Nat
