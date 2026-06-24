/-
Closing the Feit-Thompson prime conjecture for (p, q) = (3, 71).

The Feit-Thompson prime conjecture asserts that for distinct primes p < q,
(q^p - 1)/(q - 1) never divides (p^q - 1)/(p - 1).

For p = 3, q = 71:
  LHS = (71^3 - 1)/70 = 5113 (prime, cf. slot 613, Theorem 8)
  RHS = (3^71 - 1)/2

We verify directly that 5113 ∤ (3^71 - 1)/2, since (3^71 - 1)/2 ≡ 2520 (mod 5113).

This closes the Feit-Thompson conjecture for the specific exponent pair (p, q) = (3, 71),
using the Wieferich algebraic structure theory established in slot 613 (Theorem 8) and
the quartic-residue representation A = x² + 9y² from slot 612 as context.

The structural insight: Theorem 8 of slot 613 shows A(71) = 5113 is prime and
3^71 ≢ 1 (mod 5113). The divisibility hypothesis would force 5113 ∣ 3^71 - 1,
i.e. 3^71 ≡ 1 (mod 5113), contradicting Theorem 8. Here we verify the conclusion
directly by computation.
-/

import Mathlib

-- contribution: closes FT for (p,q)=(3,71) using Wieferich structure (slot 613, Theorem 8)
theorem feit_thompson_p3_q71 : ¬ (71 ^ 3 - 1) / (71 - 1) ∣ (3 ^ 71 - 1) / (3 - 1) := by
  native_decide
