import Mathlib

set_option maxHeartbeats 800000

/-!
# OEIS A239957: Bounded verification of Sun's primitive root conjecture

Zhi-Wei Sun conjectured that every prime p has a primitive root of the form k²+1.
We verify this computationally for all primes p < 50.

For each prime p, we find k ∈ {0,...,7} such that (k²+1)^d mod p ≠ 1 for all
0 < d < p-1. By Fermat's little theorem, g^(p-1) ≡ 1 mod p for all g coprime to p,
so if g^d ≢ 1 for all d < p-1, then orderOf(g) = p-1, i.e., g is a primitive root.

Covers the 15 primes: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47.

Reference: https://oeis.org/A239957
Zhi-Wei Sun, "New observations on primitive roots modulo primes", arXiv:1405.0290
-/

/-- Every prime p < 50 has a primitive root of the form k² + 1.
This verifies Zhi-Wei Sun's conjecture (OEIS A239957) for small primes.
The primitive root condition g^d % p ≠ 1 for all 0 < d < p-1 is equivalent
to orderOf(g : ZMod p) = p - 1. -/
theorem oeis_a239957_bounded_50 :
    ∀ p : Fin 50, (p : ℕ).Prime →
      ∃ k : Fin 8,
        (↑k : ℕ) ^ 2 + 1 < (↑p : ℕ) ∧
        (∀ d : Fin 50, 0 < (↑d : ℕ) → (↑d : ℕ) < (↑p : ℕ) - 1 →
          ((↑k : ℕ) ^ 2 + 1) ^ (↑d : ℕ) % (↑p : ℕ) ≠ 1) := by
  native_decide
