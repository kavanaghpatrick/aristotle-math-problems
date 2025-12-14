/-
Erdős Problem #677 - LCM of consecutive integers
OPEN: Is M(n,k) ≠ M(m,k) for all m ≥ n+k where M(n,k) = lcm(n+1,...,n+k)?

Based on FormalConjectures/ErdosProblems/677.lean

Note: The original problem asks about SAME k on both sides.
There exist solutions for DIFFERENT k values (e.g., lcm(5,6,7) = lcm(14,15)),
but the conjecture is specifically about same k.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

/-- LCM of k consecutive integers starting from n+1: lcm(n+1, n+2, ..., n+k) -/
def lcmInterval (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-- OPEN: For all m ≥ n + k, the LCMs with SAME k are different -/
theorem erdos_677 :
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k := by
  sorry

/-- Known solutions with DIFFERENT k values (these don't contradict the main conjecture):
    - lcm(5,6,7) = 210 = lcm(14,15)  [k=3 vs k=2]
    - lcm(4,5,6,7) = 420 = lcm(20,21) [k=4 vs k=2]
    Erdős expected very few such solutions where M(n, k) = M(m, l) with l > 1. -/
theorem erdos_677_different_k_example :
    lcmInterval 4 3 = lcmInterval 13 2 ∧ lcmInterval 3 4 = lcmInterval 19 2 := by
  decide

/-- Test: lcm(5,6,7) = 210 -/
theorem lcmInterval_4_3 : lcmInterval 4 3 = 210 := by
  unfold lcmInterval
  native_decide

/-- Test: lcm(14,15) = 210 -/
theorem lcmInterval_13_2 : lcmInterval 13 2 = 210 := by
  unfold lcmInterval
  native_decide

/-- Test: lcm(4,5,6,7) = 420 -/
theorem lcmInterval_3_4 : lcmInterval 3 4 = 420 := by
  unfold lcmInterval
  native_decide

/-- Test: lcm(20,21) = 420 -/
theorem lcmInterval_19_2 : lcmInterval 19 2 = 420 := by
  unfold lcmInterval
  native_decide

/-- Sanity check: For small same-k cases, the LCMs are different.
    lcm(2,3) = 6 ≠ 20 = lcm(4,5) -/
theorem erdos_677_small_check :
    lcmInterval 1 2 ≠ lcmInterval 3 2 := by
  unfold lcmInterval
  native_decide
