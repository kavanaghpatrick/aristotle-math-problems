import Mathlib

open scoped BigOperators Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Erdős Problem 373 (Hickerson's Conjecture)

Hickerson conjectured that `16! = 14! · 5! · 2!` is the largest solution to
`n! = a₁! · a₂! ··· aₖ!` with `n − 1 > a₁ ≥ a₂ ≥ ··· ≥ aₖ > 1`.

This is distinct from the Surányi case `n! = a! · b!` (k = 2).

## Status

**OPEN.** `(16, [14, 5, 2])` is the largest known multi-factorial solution;
Hickerson's maximality conjecture is unresolved.
-/

namespace Erdos373

/-- The set `S` of valid factorial-product decompositions: pairs `(n, l)` where
`l = [a₁, a₂, …, aₖ]` is a list of natural numbers satisfying:
- `l` is sorted in descending order,
- every element of `l` is at least 2,
- the largest element is strictly less than `n - 1`,
- `n! = a₁! · a₂! ··· aₖ!`. -/
def S : Set (ℕ × List ℕ) :=
  { s | let n := s.1; let l := s.2;
        l ≠ [] ∧
        l.Pairwise (· ≥ ·) ∧
        (∀ a ∈ l, 2 ≤ a) ∧
        (∀ a ∈ l, a + 1 < n) ∧
        n ! = (l.map (·!)).prod }

private theorem pairwise_16 : ([14, 5, 2] : List ℕ).Pairwise (· ≥ ·) := by
  simp [List.pairwise_cons]

private theorem pairwise_9 : ([7, 3, 3, 2] : List ℕ).Pairwise (· ≥ ·) := by
  simp [List.pairwise_cons]

private theorem pairwise_10a : ([7, 6] : List ℕ).Pairwise (· ≥ ·) := by
  simp [List.pairwise_cons]

private theorem pairwise_10b : ([7, 5, 3] : List ℕ).Pairwise (· ≥ ·) := by
  simp [List.pairwise_cons]

/-- `(16, [14, 5, 2])` is a valid factorial-product decomposition. -/
theorem mem_S_16 : (16, [14, 5, 2]) ∈ S := by
  exact ⟨by simp, pairwise_16,
    by intro a ha; simp at ha; omega,
    by intro a ha; simp at ha; omega,
    by native_decide⟩

/-- Other known solutions also belong to `S`. -/
theorem mem_S_9 : (9, [7, 3, 3, 2]) ∈ S := by
  exact ⟨by simp, pairwise_9,
    by intro a ha; simp at ha; omega,
    by intro a ha; simp at ha; omega,
    by native_decide⟩

theorem mem_S_10a : (10, [7, 6]) ∈ S := by
  exact ⟨by simp, pairwise_10a,
    by intro a ha; simp at ha; omega,
    by intro a ha; simp at ha; omega,
    by native_decide⟩

theorem mem_S_10b : (10, [7, 5, 3]) ∈ S := by
  exact ⟨by simp, pairwise_10b,
    by intro a ha; simp at ha; omega,
    by intro a ha; simp at ha; omega,
    by native_decide⟩

/-- **Hickerson's Conjecture (Erdős Problem 373):**
`(16, [14, 5, 2])` is a member of `S`, and `16` is the largest first component
among all elements of `S`.

The membership part is proved; the maximality part is an **open conjecture**. -/
theorem erdos_373_variants_maximal_solution :
    (16, [14, 5, 2]) ∈ S ∧ ∀ s ∈ S, s.fst ≤ 16 := by
  constructor
  · exact mem_S_16
  · -- OPEN CONJECTURE: Hickerson's maximality conjecture is unresolved.
    sorry

end Erdos373
