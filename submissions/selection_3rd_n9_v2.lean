/-
Algorithm Discovery: Find 3rd smallest in 9 elements

GOAL: Prove existence of a comparison-based algorithm that finds
the 3rd smallest element in 9 elements using ≤11 comparisons.

Current best: 12 comparisons
Target: ≤11 comparisons
Lower bound: 10 (information-theoretic)

Simplified formalization focusing on what Aristotle can actually search.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

/-- A comparison tree for selecting an element from n items.
    Each internal node compares elements at two indices.
    Each leaf returns the index of the selected element. -/
inductive CmpTree (n : ℕ) where
  | leaf : Fin n → CmpTree n
  | node : Fin n → Fin n → CmpTree n → CmpTree n → CmpTree n

/-- Depth (worst-case comparisons) of a comparison tree -/
def CmpTree.depth : CmpTree n → ℕ
  | .leaf _ => 0
  | .node _ _ l r => 1 + max l.depth r.depth

/-- Execute the tree given a comparison oracle (true if first < second) -/
def CmpTree.eval (t : CmpTree n) (cmp : Fin n → Fin n → Bool) : Fin n :=
  match t with
  | .leaf i => i
  | .node i j l r => if cmp i j then l.eval cmp else r.eval cmp

/-- The rank of element at index i in a list (0-indexed, smaller = lower rank) -/
def rankOf {α : Type*} [DecidableEq α] [LinearOrder α] (xs : List α) (i : Fin xs.length) : ℕ :=
  (xs.filter (· < xs[i])).length

/-- A tree correctly finds the kth smallest if for ALL orderings,
    the returned index has rank exactly k-1 (0-indexed) -/
def CmpTree.findsKth (t : CmpTree n) (k : ℕ) : Prop :=
  ∀ (xs : List ℕ), xs.length = n → xs.Nodup →
    let cmp := fun i j => decide (xs[i.val]'(by omega) < xs[j.val]'(by omega))
    let result := t.eval cmp
    (xs.filter (· < xs[result.val]'(by omega))).length = k - 1

/-- MAIN THEOREM: There exists a tree that finds 3rd smallest in 9 elements
    using at most 11 comparisons.

    A constructive proof provides the algorithm explicitly. -/
theorem exists_select_3rd_of_9_in_11 :
    ∃ t : CmpTree 9, t.findsKth 3 ∧ t.depth ≤ 11 := by
  sorry

/-- Stronger version: can we do it in 10? -/
theorem exists_select_3rd_of_9_in_10 :
    ∃ t : CmpTree 9, t.findsKth 3 ∧ t.depth ≤ 10 := by
  sorry
