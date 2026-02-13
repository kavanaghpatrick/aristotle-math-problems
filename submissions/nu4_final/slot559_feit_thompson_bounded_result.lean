/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 57a59cdf-04e2-4a98-9690-84b2ab788f96

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


/-!
# Feit-Thompson Prime Conjecture — Bounded Verification (q < 20)

Verifies that for all prime pairs p < q with q < 20, the divisibility
(q^p - 1)/(q-1) ∣ (p^q - 1)/(p-1) does NOT hold.

This covers all 28 pairs of distinct primes below 20:
(2,3), (2,5), (2,7), (2,11), (2,13), (2,17), (2,19),
(3,5), (3,7), (3,11), (3,13), (3,17), (3,19),
(5,7), (5,11), (5,13), (5,17), (5,19),
(7,11), (7,13), (7,17), (7,19),
(11,13), (11,17), (11,19),
(13,17), (13,19),
(17,19)

Reference: https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_conjecture
Computationally verified for all primes up to 10^14 (Stephens 1971, Le & Jones 2002).
-/

/-- Feit-Thompson prime conjecture verified for all prime pairs p < q < 20. -/
theorem feit_thompson_primes_bounded_20 :
    ∀ p q : Fin 20, (p : ℕ).Prime → (q : ℕ).Prime → (p : ℕ) < (q : ℕ) →
    ¬ ((q : ℕ) ^ (p : ℕ) - 1) / ((q : ℕ) - 1) ∣
      ((p : ℕ) ^ (q : ℕ) - 1) / ((p : ℕ) - 1) := by
  native_decide