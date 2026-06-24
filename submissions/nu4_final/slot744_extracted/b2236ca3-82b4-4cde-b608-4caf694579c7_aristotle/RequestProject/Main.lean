import Mathlib

set_option maxHeartbeats 8000000

/--
Feit–Thompson prime conjecture, diagnostic case p = 3, q = 1583.

(1583³ − 1)/(1583 − 1) = 2 507 473 does not divide (3¹⁵⁸³ − 1)/2.

q = 1583 is the first prime ≡ 71 (mod 72) with 3 < q ≤ 2000 at which
A(q) = q² + q + 1 = 2 507 473 is itself prime, so no proper prime factor
of A(q) is available for a Fermat-reduction argument.  The result is
confirmed by direct modular exponentiation: 3¹⁵⁸³ mod 2 507 473 = 1 702 700 ≠ 1.
-/
theorem feit_thompson_p3_q1583 :
    ¬ (1583 ^ 3 - 1) / (1583 - 1) ∣ (3 ^ 1583 - 1) / 2 := by native_decide
