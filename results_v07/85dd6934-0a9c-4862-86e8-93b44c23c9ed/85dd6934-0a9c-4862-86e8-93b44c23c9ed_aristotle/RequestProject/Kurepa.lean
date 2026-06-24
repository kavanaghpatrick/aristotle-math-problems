import Mathlib

/-!
# Kurepa's Conjecture

**Conjecture (Đuro Kurepa, 1971):** For every odd prime `p`, the left factorial
`!p = 0! + 1! + ⋯ + (p-1)!` is not divisible by `p`.

## Status

This is an **open problem** as of 2024.

### Computational verification
Verified for all primes up to `2^34` (Andrejić–Tatarevic, 2015).

### On the Barsky–Benzaghou formula
The problem statement suggested that a formula of Barsky–Benzaghou (2004) might resolve
the conjecture via a congruence implying `!p ≡ 1 (mod p)`. However, this is false in
general — direct computation shows:
- `!3 = 4 ≡ 1 (mod 3)`
- `!5 = 34 ≡ 4 (mod 5)`
- `!7 = 874 ≡ 6 (mod 7)`
- `!11 = 4037914 ≡ 1 (mod 11)`

The residues `!p mod p` take various nonzero values with no discernible pattern, and in
particular are not all congruent to `1`.

### Known connections
- By Wilson's theorem, `(p-1)! ≡ -1 (mod p)`, so the last summand is known.
- Kurepa showed his conjecture is equivalent to `gcd(!p, p!) = 2` for odd primes.
- The conjecture is connected to properties of derangement numbers and alternating
  sums of reciprocal factorials modulo `p`.

## Proof attempt

Multiple proof strategies were attempted via automated theorem proving:
1. Direct algebraic manipulation in `ZMod p` using Wilson's theorem
2. Polynomial generating function approaches
3. Recurrence-based arguments via auxiliary sequences

None succeeded, consistent with the problem's status as an open conjecture in number theory.
-/

/-- **Kurepa's Conjecture (OPEN PROBLEM)**: For every odd prime `p`, the left factorial
`!p = ∑_{i=0}^{p-1} i!` is not divisible by `p`.

This remains an open problem in number theory, verified computationally for
primes up to `2^34`. -/
theorem kurepa (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ¬ p ∣ (∑ i ∈ Finset.range p, i.factorial) := by sorry
