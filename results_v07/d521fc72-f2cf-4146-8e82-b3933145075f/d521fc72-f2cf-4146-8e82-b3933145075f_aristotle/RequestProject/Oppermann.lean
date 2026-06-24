import Mathlib

/-!
# Oppermann's Conjecture

**Statement.** For every integer x ≥ 2, there exists a prime in the interval
(x² − x, x²) and a prime in the interval (x², x² + x).

**Source:** Oppermann (1882).

**Status: OPEN.** This is a famous open conjecture in number theory. No proof
or disproof is known as of 2025.

## Implications

Oppermann's conjecture implies:
- **Legendre's conjecture**: there is always a prime between n² and (n+1)²,
  since (n+1)² = n² + 2n + 1 and x² + x < (x+1)² for all x.
- **Brocard's conjecture**: there are at least four primes between
  consecutive squares of primes (for primes ≥ 2).
- **Andrica's conjecture**: √p_{n+1} − √p_n < 1 for all n.

## Known partial results

The best unconditional prime gap result is due to Baker–Harman–Pintz (2001),
who showed there is a prime in [x, x + x^{0.525}] for all sufficiently large x.
Oppermann's conjecture would require a prime in an interval of length x^{0.5}
around x², which is far beyond current technology.

Under the Riemann Hypothesis, one can show a prime exists in
[x, x + O(√x log x)], which is still not strong enough to imply Oppermann.
-/

/-- Oppermann's conjecture: for every x ≥ 2, there is a prime in (x²−x, x²)
and a prime in (x², x²+x). This is an open problem. -/
theorem oppermann (x : ℕ) (hx : x ≥ 2) :
    (∃ p, Nat.Prime p ∧ x^2 - x < p ∧ p < x^2) ∧
    (∃ p, Nat.Prime p ∧ x^2 < p ∧ p < x^2 + x) := by sorry
