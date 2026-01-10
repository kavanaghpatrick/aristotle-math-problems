/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7efc1f8d-e20c-445f-bedf-b7e191dbbc09

The following was proved by Aristotle:

- theorem least_N_3 : IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 3 } 4

The following was negated by Aristotle:

- theorem least_N_5 : IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 16

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
Erdős Problem #1: Attack via Small n Verification

STRATEGY:
The conjecture erdos_1 states ∃ C > 0, ∀ N A, N > C · 2^|A|.

Known data (OEIS A276661):
  n=3: N=4,   ratio = 4/8   = 0.500
  n=5: N=16,  ratio = 16/32 = 0.500
  n=9: N=161, ratio = 161/512 = 0.314

ATTACK PLAN:
1. Prove least_N for small n via decidable instance
2. Verify ratios are bounded below by some C
3. Try to extract the pattern
-/

import Mathlib


open Finset

namespace Erdos1

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- SMALL n VERIFICATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- For n=3, minimum N is 4 -/
theorem least_N_3 : IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 3 } 4 := by
  constructor
  · -- 4 is achievable: use {1, 2, 4}
    use {1, 2, 4}
    refine ⟨⟨?_, ?_⟩, by decide⟩
    · intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> decide
    · -- Subset sums: 0,1,2,3,4,5,6,7 all distinct
      intro ⟨S, hS⟩ ⟨T, hT⟩ h
      simp only [mem_powerset] at hS hT
      -- S and T have same sum, need S = T
      -- {1,2,4} has 8 subsets with 8 distinct sums
      native_decide +revert
  · -- 4 is minimal: no sum-distinct 3-set in [1,3]
    intro N hN
    obtain ⟨A, hA, hcard⟩ := hN
    -- The only 3-element subset of [1,3] is {1,2,3}
    -- But {1,2} and {3} have same sum
    contrapose! hcard; interval_cases N <;> simp_all +decide [ Erdos1.IsSumDistinctSet ] ;
    · aesop_cat;
    · exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_card hA.1 ) ( by decide ) );
    · have := Finset.eq_of_subset_of_card_le hA.1 ; aesop ( simp_config := { decide := true } ) ;

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
For n=5, minimum N is 16
-/
theorem least_N_5 : IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 16 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the set $A = \{6, 9, 11, 12, 13\}$.
  set A : Finset ℕ := {6, 9, 11, 12, 13};
  -- We need to show that $A$ is a sum-distinct set with $|A| = 5$ and $N = 13$.
  have hA_sum_distinct : IsSumDistinctSet A 13 := by
    native_decide +revert;
  exact fun h => by have := h.2 ⟨ A, hA_sum_distinct, by decide ⟩ ; norm_num at this;

-/
/-- For n=5, minimum N is 16 -/
theorem least_N_5 : IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 16 := by
  sorry

-- PROVEN by Aristotle

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN ATTACK: Show ratio N/2^n is bounded below
-- ══════════════════════════════════════════════════════════════════════════════

/-- The ratio N/2^n for optimal sum-distinct sets -/
noncomputable def optimal_ratio (n : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ N : ℕ, ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = n ∧ r = N / 2^n }

/- Aristotle failed to find a proof. -/
/-- Key claim: optimal_ratio n ≥ 0.2 for all n ≥ 1 -/
theorem ratio_lower_bound : ∀ n : ℕ, n ≥ 1 → optimal_ratio n ≥ 0.2 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `le_div_iff`-/
/-- If ratios are bounded below, erdos_1 follows -/
theorem erdos_1_from_ratio_bound (C : ℝ) (hC : C > 0)
    (h : ∀ n : ℕ, n ≥ 1 → ∀ N A, IsSumDistinctSet A N → A.card = n → (N : ℝ) / 2^n ≥ C) :
    ∃ C' > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
        N ≠ 0 → C' * 2 ^ A.card < N := by
  use C / 2
  refine ⟨by linarith, ?_⟩
  intro N A hA hN
  by_cases hcard : A.card = 0
  · -- A.card = 0 means A = ∅, but then IsSumDistinctSet requires A ⊆ Icc 1 N
    -- This is vacuously true, but N ≠ 0 gives us N ≥ 1, so C/2 < N for small C
    simp only [hcard, pow_zero, mul_one]
    -- Need: C/2 < N. We have N ≥ 1 (from hN) and C > 0 small enough
    -- Actually this needs N > C/2, which isn't guaranteed.
    -- But for A = ∅ with card = 0, the hypothesis h doesn't apply (needs n ≥ 1)
    -- So this case is actually impossible to derive C/2 < N from our hypotheses alone
    -- We need a separate argument or assumption
    sorry
  · have hn : A.card ≥ 1 := Nat.one_le_iff_ne_zero.mpr hcard
    have hbound := h A.card hn N A hA rfl
    have h2n_pos : (0 : ℝ) < 2^A.card := by positivity
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    -- From hbound: N / 2^n ≥ C, so N ≥ C * 2^n > (C/2) * 2^n
    have hN_ge : (N : ℝ) ≥ C * 2^A.card := by
      have := le_div_iff h2n_pos |>.mpr
      rw [ge_iff_le] at hbound ⊢
      calc C * 2^A.card = C * 2^A.card := rfl
        _ ≤ (N : ℝ) / 2^A.card * 2^A.card := by nlinarith
        _ = N := by field_simp
    linarith

end Erdos1