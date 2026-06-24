import Mathlib

/-!
# Erdős Problem 828

Are there infinitely many `n` with `φ(n) ∣ (n + 1)`?

## Status: OPEN

This is an open problem in number theory. Nine solutions are known (OEIS A203966):
  1, 2, 3, 15, 255, 65535, 83623935, 4294967295, 6992962672132095.

### Chain construction
If `2φ(n) = n + 1` and `n + 2` is prime, then `m = n(n + 2)` also satisfies
`2φ(m) = m + 1`. This generates:
  1 → 3 → 15 → 255 → 65535 → 4294967295.

### Known properties
Any solution with `n > 2` must be odd and squarefree, with
`gcd(n, φ(n)) = 1`.

### Heuristic evidence
Heuristic arguments suggest there may be only finitely many solutions,
making the infinitude conjecture likely **false** — but neither direction
has been proved.

## What is proved here

We verify several known solutions computationally. The main infinitude
statement remains `sorry` as it is an open problem.
-/

section KnownSolutions

-- Verify that φ(n) ∣ (n + 1) for the small known solutions.
example : Nat.totient 1 ∣ (1 + 1) := by native_decide
example : Nat.totient 2 ∣ (2 + 1) := by native_decide
example : Nat.totient 3 ∣ (3 + 1) := by native_decide
example : Nat.totient 15 ∣ (15 + 1) := by native_decide
example : Nat.totient 255 ∣ (255 + 1) := by native_decide
example : Nat.totient 65535 ∣ (65535 + 1) := by native_decide

end KnownSolutions

/-- **Erdős Problem 828 (OPEN).**
There are infinitely many `n` with `n > 0` and `φ(n) ∣ (n + 1)`.

This is an open problem. Nine solutions are known, but it is unknown whether
there are infinitely many. Heuristic evidence suggests finitely many solutions.
The statement is left as `sorry`. -/
theorem erdos828 :
    Set.Infinite {n : ℕ | n > 0 ∧ Nat.totient n ∣ (n + 1)} := by
  sorry
