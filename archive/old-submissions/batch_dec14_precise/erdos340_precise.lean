/-
Erdős Problem #340 - Greedy Sidon Sequence Growth
OPEN: Does the greedy Sidon sequence grow like N^{1/2 - ε}?

Based on FormalConjectures/ErdosProblems/340.lean
-/

import Mathlib

set_option maxHeartbeats 400000

open Filter Finset
open scoped Real Pointwise

/-- Given a finite Sidon set `A` and a lower bound `m`, finds the smallest number `m' ≥ m`
such that `A ∪ {m'}` is Sidon. -/
private def greedySidon.go (A : Finset ℕ) (hA : IsSidon A) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (A ∪ {m'})} :=
  if h : A.Nonempty then
    ⟨Nat.find (hA.exists_insert_ge h m), Nat.find_spec (hA.exists_insert_ge h m)⟩
  else ⟨m, by simp_all [IsSidon]⟩

/-- Main search loop for generating the greedy Sidon sequence. -/
private def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon A} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A ∪ {s'.1}, s'.2.2.2⟩, s')

/-- `greedySidon` is the sequence obtained by starting with {1} and iteratively
obtaining the next smallest integer that preserves the Sidon property.
This gives the sequence 1, 2, 4, 8, 13, 21, 31, ... -/
def greedySidon (n : ℕ) : ℕ := greedySidon.aux n |>.2

/-- Test: greedySidon(0) = 1 -/
theorem greedySidon_zero : greedySidon 0 = 1 := rfl

/-- Test: greedySidon(1) = 2 -/
theorem greedySidon_one : greedySidon 1 = 2 := by decide

/-- Test: greedySidon(2) = 4 -/
theorem greedySidon_two : greedySidon 2 = 4 := by decide

/-- Test: greedySidon(3) = 8 -/
theorem greedySidon_three : greedySidon 3 = 8 := by decide

/-- Test: greedySidon(4) = 13 -/
theorem greedySidon_four : greedySidon 4 = 13 := by decide

/-- Test: greedySidon(5) = 21 -/
theorem greedySidon_five : greedySidon 5 = 21 := by decide

/-- OPEN: Is |A ∩ {1,...,N}| >> N^{1/2 - ε} for all ε > 0?
Equivalently: √n / n^ε = O(|A ∩ [1,n]|) -/
theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ √n / n ^ ε) =O[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ) := by
  sorry

/-- Variant: Does A - A have positive density? -/
theorem erdos_340_sub_hasPosDensity :
    Set.HasPosDensity (Set.range greedySidon - Set.range greedySidon) :=
  sorry

/-- Variant: Is 22 in A - A? (Known to be yes) -/
theorem erdos_340_22_mem_sub :
    22 ∈ Set.range greedySidon - Set.range greedySidon := by
  sorry

/-- Variant: Is 33 in A - A? (Unknown) -/
theorem erdos_340_33_mem_sub :
    33 ∈ Set.range greedySidon - Set.range greedySidon ↔ sorry :=
  sorry
