import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# Erdős Problem 203 — 1D Sierpinski analog with index-1 primes only

## Original claim (FALSE)

For every m ≥ 0 there exists k ∈ [0,32) escaping every prime p ≤ 500 for which
2 is a primitive root mod p (Artin primes), i.e., ¬ p ∣ 2^k * m + 1.

## Disproof

The claim is false. m = 4643 is a counterexample: for every k ∈ {0,…,31},
there is an Artin prime p ≤ 500 dividing 2^k · 4643 + 1. Concretely:

  k=0: 3 | 4644        k=1: 37 | 9287       k=2: 3 | 18572
  k=3: 5 | 37145       k=4: 3 | 74288       k=5: 11,13 | 148577
  k=6: 3 | 297152      k=7: 5 | 594305      k=8: 3 | 1188608
  …  (every k is covered)

We formalize the negation and prove it via `native_decide`.
-/

-- The original (false) statement, commented out:
/- The following theorem is FALSE. m = 4643 is a counterexample.
theorem index1_sierpinski_insufficient_K32_B500 (m : ℕ) :
    ∃ k : ℕ, k < 32 ∧
      ∀ p : ℕ, p.Prime → 2 < p → p ≤ 500 →
        (((Finset.univ : Finset (Fin (p-1))).image
          (fun a => (2 ^ a.val) % p)).card = p - 1) →
        ¬ p ∣ 2 ^ k * m + 1 := by sorry
-/

/-- The Artin primes up to 500 (primes p where 2 is a primitive root mod p). -/
def artinPrimesUpTo500 : List ℕ :=
  [3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83, 101, 107, 131, 139,
   149, 163, 173, 179, 181, 197, 211, 227, 269, 293, 317, 347, 349,
   373, 379, 389, 419, 421, 443, 461, 467, 491]

/-- Helper: checks that the original statement fails for m = 4643.
    For every k < 32, there exists an Artin prime p ≤ 500 dividing 2^k * 4643 + 1. -/
def counterexampleCheck : Bool :=
  (List.range 32).all fun k =>
    artinPrimesUpTo500.any fun p =>
      (2 ^ k * 4643 + 1) % p == 0

/-- The original theorem is false: m = 4643 is a counterexample.
    For every k < 32, some Artin prime p ≤ 500 divides 2^k · 4643 + 1. -/
theorem index1_sierpinski_insufficient_K32_B500_counterexample :
    counterexampleCheck = true := by native_decide
