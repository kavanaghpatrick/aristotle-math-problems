import Mathlib

/--
Erdős Problem 1003: Are there infinitely many n with φ(n) = φ(n+1)?

Status: OPEN. This is a well-known open problem in number theory posed by Paul Erdős.

Many computational examples are known: n = 1, 3, 15, 104, 164, 194, 255, 495, 584, 975, ...
(where φ(n) = φ(n+1) for each of these n).

Erdős, Pomerance, and Sárközy (1987) proved an upper bound on the counting function:
the number of such n ≤ x is at most x/exp(c·(log x)^{1/3}) for some constant c > 0.

No proof of infinitude is currently known in the mathematical literature.
-/
theorem erdos_1003 :
    Set.Infinite {n : ℕ | Nat.totient n = Nat.totient (n + 1)} := by sorry
