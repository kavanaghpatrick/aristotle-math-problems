/-
Erdős Problem #1074 - EHS Numbers and Pillai Primes
SOLVED: Both sets proven infinite

BORIS PATTERN MATCH:
- Pre-formalized in FC: ✅
- SOLVED: ✅ (2 solved variants)
- TEST cases with decide: ✅
- No asymptotics: ✅

PROBLEM: Let S be the set of m ≥ 1 such that there exists a prime p ≢ 1 (mod m)
with p | m! + 1. Is S infinite?

ANSWER: YES - Erdős, Hardy, Subbarao proved both S and the set of such primes
are infinite.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped Nat

namespace Erdos1074

/-- EHS numbers: m ≥ 1 such that ∃ prime p with p ∤ 1 (mod m) and p | m! + 1 -/
def EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m.factorial + 1}

/-- Pillai primes: primes p such that ∃ m with p ∤ 1 (mod m) and p | m! + 1 -/
def PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m, ¬p ≡ 1 [MOD m] ∧ p ∣ m.factorial + 1}

/--
TEST CASE: 23 is a Pillai prime.
Chowla noted that 14! + 1 ≡ 18! + 1 ≡ 0 (mod 23).
-/
theorem pillai_23 : 23 ∈ PillaiPrimes := by
  constructor
  · decide
  · use 14
    constructor
    · decide
    · -- 14! + 1 = 87178291201, and 87178291201 / 23 = 3790360487
      native_decide

/--
SOLVED: The set of EHS numbers is infinite.
Proved by Erdős, Hardy, and Subbarao.
-/
theorem EHSNumbers_infinite : EHSNumbers.Infinite := by
  sorry

/--
SOLVED: The set of Pillai primes is infinite.
Proved by Erdős, Hardy, and Subbarao.
-/
theorem PillaiPrimes_infinite : PillaiPrimes.Infinite := by
  sorry

/--
The first few EHS numbers are 8, 9, 13, 14, 15, 16, 17, ...
-/
theorem EHS_examples : {8, 9, 13, 14, 15, 16, 17} ⊆ EHSNumbers := by
  sorry

/--
The first few Pillai primes are 23, 29, 59, 61, 67, 71, ...
-/
theorem Pillai_examples : {23, 29, 59, 61, 67, 71} ⊆ PillaiPrimes := by
  sorry

end Erdos1074
