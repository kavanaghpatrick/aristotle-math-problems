import Mathlib

/-!
# Brocard's Problem

Brocard's problem (1876) asks: for which positive integers `n` is `n! + 1` a perfect square?

The only known solutions are:
- `n = 4`: `4! + 1 = 25 = 5²`
- `n = 5`: `5! + 1 = 121 = 11²`
- `n = 7`: `7! + 1 = 5041 = 71²`

It is conjectured that there are no other solutions. This has been verified computationally
for `n ≤ 10⁹` by Berndt and Galway (2000).

## Status

**This is an open problem.** No proof is known for the general case `n ≥ 8`.
The ABC conjecture would imply that there are only finitely many solutions.

The theorem below remains unproved (`sorry`). No known mathematical technique
suffices to prove it:
- Modular arithmetic cannot work alone because `n! + 1 ≡ 1 (mod p)` for all
  primes `p ≤ n`, and `1` is always a quadratic residue.
- Growth-rate arguments show solutions become increasingly sparse but cannot
  rule them out entirely.
- The strongest conditional result (assuming ABC) gives only finiteness, not
  an effective bound.

## References

- Brocard, H. (1876). Question 166. Nouv. Corresp. Math. 2, 287.
- Ramanujan, S. (1913). Question 469. J. Indian Math. Soc. 5, 59.
- Berndt, B. C. and Galway, W. F. (2000). The Brocard–Ramanujan diophantine
  equation n! + 1 = m². The Ramanujan Journal, 4, 41–42.
-/

/-- Brocard's problem: for n ≥ 8, n! + 1 is never a perfect square.
    **Open problem** — left as `sorry`. -/
theorem brocard (n : ℕ) (hn : n ≥ 8) :
    ¬ ∃ m : ℕ, n.factorial + 1 = m ^ 2 := by sorry
