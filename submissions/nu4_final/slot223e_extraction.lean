/-
  slot223e_extraction.lean

  HELPER LEMMA: Extract u, w from a 3-element Finset containing v.

  Given T with |T| = 3 and v ∈ T, there exist u, w with:
  - u ∈ T, w ∈ T
  - u ≠ v, w ≠ v, u ≠ w
  - T = {v, u, w}

  1 SORRY for Aristotle.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- From a 3-element Finset containing v, extract the other two elements -/
lemma extract_two_from_triple (T : Finset V) (v : V)
    (hv : v ∈ T) (hcard : T.card = 3) :
    ∃ u w, u ∈ T ∧ w ∈ T ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ T = {v, u, w} := by
  -- T \ {v} has exactly 2 elements
  have h_erase_card : (T.erase v).card = 2 := by
    rw [card_erase_of_mem hv, hcard]
    norm_num
  -- Extract the two elements from T \ {v}
  obtain ⟨u, w, hu_mem, hw_mem, huw, h_eq⟩ := card_eq_two.mp h_erase_card
  -- u, w ∈ T and ≠ v (since they're in T.erase v)
  have hu_T : u ∈ T := mem_of_mem_erase hu_mem
  have hw_T : w ∈ T := mem_of_mem_erase hw_mem
  have huv : u ≠ v := ne_of_mem_erase hu_mem
  have hwv : w ≠ v := ne_of_mem_erase hw_mem
  use u, w, hu_T, hw_T, huv, hwv, huw
  -- Show T = {v, u, w}
  ext x
  simp only [mem_insert]
  constructor
  · intro hx
    by_cases hxv : x = v
    · left; exact hxv
    · right
      have : x ∈ T.erase v := mem_erase.mpr ⟨hxv, hx⟩
      rw [h_eq] at this
      exact this
  · intro hx
    rcases hx with rfl | hx
    · exact hv
    · have : x ∈ T.erase v := by rw [h_eq]; exact hx
      exact mem_of_mem_erase this

end
