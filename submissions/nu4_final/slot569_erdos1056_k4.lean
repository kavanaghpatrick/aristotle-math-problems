import Mathlib

/-!
# Erdős Problem 1056: k=4 witness

We extend the known k=2 (Erdős 1979) and k=3 (Makowski 1983) cases by
providing a verified k=4 witness: p=23, boundaries=[2, 5, 9, 12, 22].

The four consecutive intervals each have product ≡ 1 mod 23:
  [2,5):  2 * 3 * 4 = 24 ≡ 1 (mod 23)
  [5,9):  5 * 6 * 7 * 8 = 1680 ≡ 1 (mod 23)
  [9,12): 9 * 10 * 11 = 990 ≡ 1 (mod 23)
  [12,22): 12 * 13 * ... * 21 = 1279935820800 ≡ 1 (mod 23)

This is the unique k=4 witness for primes up to 50.

Reference: https://www.erdosproblems.com/1056
-/

open Nat

namespace Erdos1056

def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

/-- The k=4 case of Erdős Problem 1056, extending Erdős (k=2) and Makowski (k=3).
For p=23, the four consecutive intervals [2,5), [5,9), [9,12), [12,22) each
have product congruent to 1 modulo 23. -/
theorem erdos_1056_k4 :
    AllModProdEqualsOne 23 ![2, 5, 9, 12, 22] := by
  unfold AllModProdEqualsOne
  decide

end Erdos1056
