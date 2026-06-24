import Mathlib

/-- A natural number `n` is `k`-full if for every prime `p` dividing `n`, `p ^ k` divides `n`.
Equivalently, every exponent in the prime factorization of `n` is at least `k`.
For example, 8 = 2³ is 3-full, and 36 = 2² · 3² is 2-full. -/
def Nat.Full (k n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ k ∣ n

/-- Erdős Problem 366: There is no 2-full `n > 0` such that `n + 1` is 3-full.

This is an **open problem** in number theory. The expected answer is that no such `n` exists.
Note: The reverse direction exists: 8 is 3-full and 9 = 8 + 1 is 2-full.

The conjecture would follow from the ABC conjecture: if `n` is 2-full then `rad(n) ≤ n^(1/2)`,
and if `n+1` is 3-full then `rad(n+1) ≤ (n+1)^(1/3)`. Applying ABC to `n + 1 = (n+1)` with
`a = n, b = 1, c = n+1` gives `n+1 ≤ K_ε · (rad(n) · rad(n+1))^(1+ε) ≤ K_ε · n^((5/6)(1+ε))`,
which is a contradiction for large `n` when `ε < 1/5`. -/
theorem erdos_366 :
    ¬ ∃ n : ℕ, n > 0 ∧ Nat.Full 2 n ∧ Nat.Full 3 (n + 1) := by
  sorry
