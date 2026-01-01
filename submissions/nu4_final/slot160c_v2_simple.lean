/-
Tuza ν=4: sum_eq_card_implies_all_one - Arithmetic lemma

GOAL: If M.sum w = |M| and each w(m) ≤ 1, then all w(m) = 1.

This is the key arithmetic fact for LP optimality.

1 SORRY: The pigeonhole-style argument.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {α : Type*} [DecidableEq α]

/-- If a finite sum equals the count and each term is at most 1, all terms equal 1. -/
theorem sum_eq_card_implies_all_one (M : Finset α) (w : α → ℝ)
    (h_sum : M.sum w = M.card)
    (h_nonneg : ∀ m ∈ M, 0 ≤ w m)
    (h_bounded : ∀ m ∈ M, w m ≤ 1) :
    ∀ m ∈ M, w m = 1 := by
  -- If any w(m) < 1, then sum < |M|, contradiction
  by_contra h
  push_neg at h
  obtain ⟨m₀, hm₀, hlt⟩ := h
  have h_strict : w m₀ < 1 := lt_of_le_of_ne (h_bounded m₀ hm₀) hlt
  have h_sum_lt : M.sum w < M.card := by
    calc M.sum w = w m₀ + (M.erase m₀).sum w := by
           rw [← Finset.add_sum_erase M w hm₀]
         _ < 1 + (M.erase m₀).sum w := by linarith
         _ ≤ 1 + (M.erase m₀).sum (fun _ => (1 : ℝ)) := by
           apply add_le_add_left
           apply Finset.sum_le_sum
           intro x hx
           exact h_bounded x (Finset.mem_of_mem_erase hx)
         _ = 1 + (M.erase m₀).card := by simp
         _ = 1 + ((M.card : ℝ) - 1) := by
             rw [Finset.card_erase_of_mem hm₀]
             simp [Nat.cast_sub (Finset.one_le_card.mpr ⟨m₀, hm₀⟩)]
         _ = M.card := by ring
  linarith
