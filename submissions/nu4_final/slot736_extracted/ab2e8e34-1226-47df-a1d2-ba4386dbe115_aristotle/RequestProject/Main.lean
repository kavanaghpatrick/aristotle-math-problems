import Mathlib

set_option maxHeartbeats 8000000

/--
The Feit-Thompson prime conjecture for p = 3 and primes q ≡ 71 (mod 72) with q ≤ 1500.

For distinct primes p < q, the Feit-Thompson conjecture asserts that
(q^p - 1)/(q - 1) does not divide (p^q - 1)/(p - 1).

This theorem verifies the conjecture for p = 3 and all primes q in the
arithmetic progression q ≡ 71 (mod 72) up to 1500, namely:
{71, 359, 431, 503, 647, 719, 863, 1151, 1223, 1367, 1439}.
-/
theorem feit_thompson_p3_q71_family_1500 :
    ∀ q : ℕ, q.Prime → 3 < q → q ≡ 71 [MOD 72] → q ≤ 1500 →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 := by
  suffices h : ∀ q ∈ Finset.range 1501, q.Prime → 3 < q → q ≡ 71 [MOD 72] →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 by
    intro q hq1 hq2 hq3 hq4
    exact h q (Finset.mem_range.mpr (by omega)) hq1 hq2 hq3
  native_decide
