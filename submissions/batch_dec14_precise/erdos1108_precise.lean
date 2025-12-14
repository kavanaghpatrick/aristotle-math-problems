/-
Erdos Problem #1108 - Factorial Sums and Powers
OPEN: Does the set of factorial sums contain only finitely many k-th powers?

SIMPLE definitions - uses only Mathlib:
- Nat.factorial
- Finset, summation
- Set.Finite
-/

import Mathlib

set_option maxHeartbeats 400000

open Nat Finset

namespace Erdos1108

/-- The set A of all finite sums of distinct factorials.
    EXACT definition from FormalConjectures. -/
def FactorialSums : Set ℕ :=
  {m : ℕ | ∃ S : Finset ℕ, m = ∑ n ∈ S, n.factorial}

/-- A number is powerful if each prime factor appears with exponent >= 2.
    EXACT definition from FormalConjectures. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- OPEN: For each k >= 2, does A contain only finitely many k-th powers? -/
theorem erdos_1108_kth_powers : (∀ k ≥ 2,
    Set.Finite { a | a ∈ FactorialSums ∧ ∃ m : ℕ, m ^ k = a }) ↔ sorry := by
  sorry

/-- OPEN: Does A contain only finitely many powerful numbers? -/
theorem erdos_1108_powerful :
     {a ∈ FactorialSums | IsPowerful a}.Finite ↔ sorry := by
  sorry

/-- Test: 1! = 1 is in FactorialSums. -/
theorem one_mem : 1 ∈ FactorialSums := by
  use {1}
  simp [factorial]

/-- Test: 1! + 2! = 3 is in FactorialSums. -/
theorem three_mem : 3 ∈ FactorialSums := by
  use {1, 2}
  simp [factorial]

/-- Test: 1! + 2! + 3! = 9 is in FactorialSums. -/
theorem nine_mem : 9 ∈ FactorialSums := by
  use {1, 2, 3}
  simp [factorial]

end Erdos1108
