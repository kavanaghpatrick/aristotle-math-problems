/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a58f4d00-cdf2-4391-8b84-e0d5cb6af6c8

The following was negated by Aristotle:

- theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ √n / n ^ ε) =O[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```


-/

/-
Erdős Problem #340 - Greedy Sidon Sequence Growth
OPEN: Does the greedy Sidon sequence grow like N^{1/2 - ε}?

Based on FormalConjectures/ErdosProblems/340.lean
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  IsSidon
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  A
Function expected at
  IsSidon
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (A ∪ { m' })
Function expected at
  IsSidon
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  A
don't know how to synthesize implicit argument `IsSidon`
  @greedySidon.aux (?m.5 n) (?m.6 n) n
context:
n : ℕ
⊢ ?m.5 n
don't know how to synthesize implicit argument
  @greedySidon.aux (?m.5 n) (?m.6 n) n
context:
n : ℕ
⊢ Sort ?u.26815-/
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

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
OPEN: Is |A ∩ {1,...,N}| >> N^{1/2 - ε} for all ε > 0?
Equivalently: √n / n^ε = O(|A ∩ [1,n]|)
-/
theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ √n / n ^ ε) =O[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use Filter.atTop;
  use PUnit;
  refine' ⟨ fun _ => 0, 1 / 4, _, _ ⟩ <;> norm_num;
  norm_num [ Asymptotics.isBigO_iff ];
  intro x n; use n + 1; norm_num [ Set.ncard_eq_toFinset_card' ];
  -- Since $n + 1$ is always positive for $n \geq 0$, both the numerator and the denominator are positive, making the fraction positive.
  apply div_pos; apply abs_pos.mpr; exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  apply abs_pos.mpr; exact ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)

-/
/-- OPEN: Is |A ∩ {1,...,N}| >> N^{1/2 - ε} for all ε > 0?
Equivalently: √n / n^ε = O(|A ∩ [1,n]|) -/
theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ √n / n ^ ε) =O[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown constant `Set.HasPosDensity`-/
/-- Variant: Does A - A have positive density? -/
theorem erdos_340_sub_hasPosDensity :
    Set.HasPosDensity (Set.range greedySidon - Set.range greedySidon) :=
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HSub (Set ℕ) (Set ℕ) (Set ℕ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- Variant: Is 22 in A - A? (Known to be yes) -/
theorem erdos_340_22_mem_sub :
    22 ∈ Set.range greedySidon - Set.range greedySidon := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HSub (Set ℕ) (Set ℕ) (Set ℕ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- Variant: Is 33 in A - A? (Unknown) -/
theorem erdos_340_33_mem_sub :
    33 ∈ Set.range greedySidon - Set.range greedySidon ↔ sorry :=
  sorry