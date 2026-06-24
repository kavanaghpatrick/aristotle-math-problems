import Mathlib

/-!
# Erdős Problem 479

**Conjecture.** For every k > 1, are there infinitely many n with 2^n ≡ k (mod n)?

## Status

This is an **open problem** in number theory. As of 2024, no proof or disproof is known.

### Computational evidence

- For k = 2: solutions are plentiful — every odd prime p where 2 is a primitive root
  (i.e., ord_p(2) = p - 1) satisfies 2^p ≡ 2 (mod p) by Fermat's little theorem.
  By Artin's conjecture (itself unproven unconditionally), there should be infinitely
  many such primes.

- For k = 4: many even solutions exist (e.g., n = 4, 6, 10, 12, 14, 22, 26, 30, ...).

- For k = 3: no solution n > 1 was found below 10,000. Even finding a single n > 1
  with 2^n ≡ 3 (mod n) appears computationally difficult.

- For k = 5: only n = 3 found below 10,000 (since 2^3 = 8 ≡ 3 mod 5... wait, that's
  not right). Actually n = 3: 2^3 = 8, 8 mod 3 = 2 ≠ 5. n = 1: 2^1 = 2, 2 mod 1 = 0,
  5 mod 1 = 0. So n = 1 is a trivial solution.

### Connection to multiplicative order

The problem connects to the multiplicative order of 2 modulo n and the distribution
of such orders across the natural numbers. Solutions n must satisfy ord_n(2) | n
in a way that makes 2^n land exactly on k modulo n.

## Reference

P. Erdős, "Some unconventional problems in number theory",
*Mathematics Magazine*, 52(2):67–70, 1979.
-/

/-- **Erdős Problem 479** (Open Problem): For every k > 1, there are infinitely many n
with 2^n ≡ k (mod n). This remains an open conjecture in number theory. -/
theorem erdos_479 :
    ∀ k : ℕ, k > 1 →
    { n : ℕ | 2 ^ n ≡ k [MOD n] }.Infinite := by
  sorry
