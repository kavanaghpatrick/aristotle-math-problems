import Mathlib

/--
Feit-Thompson prime conjecture at p=3, q=1583:
`(1583^3 - 1) / (1583 - 1)` does not divide `(3^1583 - 1) / 2`.

Equivalently, `3^1583 ≢ 1 (mod 2507473)` where `2507473 = 1583^2 + 1583 + 1` is prime.
The proof reduces the quotient `(1583^3 - 1)/(1583 - 1)` to `2507473` via `norm_num`,
then verifies non-divisibility by `native_decide` (a 22-bit modular exponentiation).
-/
theorem feit_thompson_p3_q1583 :
    ¬ (1583 ^ 3 - 1) / (1583 - 1) ∣ (3 ^ 1583 - 1) / 2 := by
  norm_num
  native_decide
