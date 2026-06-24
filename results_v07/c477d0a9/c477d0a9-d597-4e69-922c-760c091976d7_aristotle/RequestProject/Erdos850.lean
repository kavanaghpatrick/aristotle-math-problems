import Mathlib

/-!
# Erdős Problem 850 — No three consecutive same-radical pairs

## Conjecture
No distinct positive integers x, y satisfy
  rad(x) = rad(y), rad(x+1) = rad(y+1), and rad(x+2) = rad(y+2)
simultaneously, where rad(n) is the radical of n (product of distinct prime factors),
equivalently characterized by equality of `Nat.primeFactors`.

## Status
**OPEN.** No proof is known. Computational search to 10^8 found zero witnesses
with k = 3 consecutive matching radicals.

## Known partial results
- The k = 2 family x = 2^n − 2, y = 2^n(2^n − 2) gives infinitely many pairs with
  rad(x) = rad(y) and rad(x+1) = rad(y+1), but cannot extend to k = 3 because
  y + 2 = (2^n − 1)² + 1 always has an odd prime factor not dividing x + 2.

## Proof attempts
Two strategies were attempted:

1. **Divisibility approach**: Writing y = a·rad(x)/gcd, etc., and using coprimality of
   consecutive integers to constrain the gap y − x. The coprimality of n and n+1 forces
   primeFactors(x) ∩ primeFactors(x+1) = ∅, giving strong disjointness. However, this
   alone does not yield a finite bound on possible solutions.

2. **Radical product bound**: The gap d = y − x must simultaneously be expressible as
   differences of numbers with the same radical for three consecutive values. Writing
   d = k·rad(x) = m·rad(x+1) = n·rad(x+2) (approximately), one can show mutual
   divisibility constraints via coprimality, but establishing the crucial size bound
   k·m·n < rad(x)·rad(x+1)·rad(x+2) appears equivalent to the original conjecture.

The abc conjecture would imply this result (and much stronger statements), but the
abc conjecture itself remains unproven.
-/

theorem erdos_850_no_triple :
    ¬ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧
    x.primeFactors = y.primeFactors ∧
    (x+1).primeFactors = (y+1).primeFactors ∧
    (x+2).primeFactors = (y+2).primeFactors := by sorry
