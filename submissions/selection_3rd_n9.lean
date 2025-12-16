/-
Algorithm Discovery Problem: Find 3rd smallest in 9 elements

GOAL: Discover an algorithm that finds the 3rd smallest element
in a list of 9 distinct elements using at most 11 comparisons.

Current best known: 12 comparisons
Target: 11 comparisons (or prove 12 is optimal)
Lower bound: 10 comparisons (information theoretic)

If Aristotle constructs a proof, the witness IS the algorithm.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

/-- A comparison-based selection algorithm is a decision tree where
    each internal node compares two elements by index, and leaves
    output the index of the kth smallest element. -/
inductive SelectionTree (n : ℕ) : Type where
  | leaf : Fin n → SelectionTree n
  | compare : Fin n → Fin n → SelectionTree n → SelectionTree n → SelectionTree n
  deriving Repr

/-- Count the number of comparisons on the worst-case path -/
def SelectionTree.depth : SelectionTree n → ℕ
  | .leaf _ => 0
  | .compare _ _ left right => 1 + max left.depth right.depth

/-- Execute the selection tree on a concrete ordering.
    Returns the index that the tree outputs. -/
def SelectionTree.execute (t : SelectionTree n) (lt : Fin n → Fin n → Bool) : Fin n :=
  match t with
  | .leaf i => i
  | .compare i j left right =>
    if lt i j then left.execute lt else right.execute lt

/-- The tree correctly finds the kth smallest if, for all possible
    orderings of n distinct elements, executing the tree returns
    an index whose element is the kth smallest. -/
def SelectionTree.correct (t : SelectionTree n) (k : ℕ) : Prop :=
  ∀ (α : Type) [LinearOrder α] [DecidableRel (α := α) (· < ·)],
    ∀ (xs : List α), xs.length = n → xs.Nodup →
      let result := t.execute (fun i j =>
        decide (xs.get ⟨i.val, by omega⟩ < xs.get ⟨j.val, by omega⟩))
      -- The result index gives the kth smallest element
      (xs.toFinset.filter (· ≤ xs.get ⟨result.val, by omega⟩)).card = k

/-- DISCOVERY THEOREM:
    There exists a selection tree for 9 elements that:
    1. Correctly finds the 3rd smallest element
    2. Uses at most 11 comparisons in the worst case

    If this theorem is proven constructively, the witness 't' IS
    a new algorithm beating the current best of 12 comparisons.
-/
theorem exists_selection_3rd_in_9_with_11_comparisons :
    ∃ (t : SelectionTree 9),
      t.correct 3 ∧ t.depth ≤ 11 := by
  sorry

/-- Alternative formulation: prove or disprove 10 comparisons suffice -/
theorem exists_selection_3rd_in_9_with_10_comparisons_or_impossible :
    (∃ (t : SelectionTree 9), t.correct 3 ∧ t.depth ≤ 10) ∨
    (∀ (t : SelectionTree 9), t.correct 3 → t.depth ≥ 11) := by
  sorry
