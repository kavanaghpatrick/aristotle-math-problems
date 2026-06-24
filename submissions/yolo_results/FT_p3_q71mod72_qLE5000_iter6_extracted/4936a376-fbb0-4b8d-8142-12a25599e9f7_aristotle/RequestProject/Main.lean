import Mathlib

open scoped Nat

-- Feit-Thompson prime conjecture for p = 3, q ≡ 71 (mod 72), q ≤ 5000.
--
-- The Feit-Thompson conjecture (1962) asserts that for distinct primes p < q,
-- (q^p - 1)/(q - 1) does not divide (p^q - 1)/(p - 1).
--
-- This theorem verifies the conjecture for p = 3 and all 28 primes q ≡ 71 (mod 72)
-- with 3 < q ≤ 5000, namely:
-- {71, 359, 431, 503, 647, 719, 863, 1151, 1223, 1367, 1439, 1511, 1583,
--  1871, 2087, 2447, 2591, 2663, 2879, 3023, 3167, 3527, 3671, 4391, 4463,
--  4679, 4751, 4967}.
--
-- Proof method: finite verification via `native_decide`. The universal quantifier
-- over ℕ is reduced to `Finset.range 5001` using the bound q ≤ 5000, and each
-- candidate is checked computationally: non-primes and primes outside the residue
-- class are rejected trivially, while the 28 family primes are verified by computing
-- (3^q - 1)/2 mod (q² + q + 1) ≠ 0.

set_option maxHeartbeats 80000000 in
theorem feit_thompson_p3_q71_family_5000 :
    ∀ q : ℕ, q.Prime → 3 < q → q ≡ 71 [MOD 72] → q ≤ 5000 →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 := by
  intro q hp hlt hmod hle
  have hq : q ∈ Finset.range 5001 := Finset.mem_range.mpr (by omega)
  have key : ∀ q ∈ Finset.range 5001,
      q.Prime → 3 < q → q % 72 = 71 →
        ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 := by native_decide
  exact key q hq hp hlt hmod
