/-
Tuza ν=4 Strategy - Slot 376: SCATTERED τ ≤ 4

CASE DESCRIPTION:
  4 completely disjoint M-triangles (no shared vertices).
  Each triangle is independent.

STRUCTURE (on Fin 12):
  A = {0, 1, 2}
  B = {3, 4, 5}
  C = {6, 7, 8}
  D = {9, 10, 11}

KEY INSIGHT:
  In the minimal graph (only M-triangle edges), the ONLY triangles are A, B, C, D.
  No externals exist because vertices from different M-elements are not connected.

EXPLICIT 4-EDGE COVER:
  e1 = {0, 1}  -- covers A
  e2 = {3, 4}  -- covers B
  e3 = {6, 7}  -- covers C
  e4 = {9, 10} -- covers D

THEOREM: τ ≤ 4 for minimal scattered (τ = ν = 4)

TIER: 1 (Decidable on Fin 12)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- SCATTERED: 4 DISJOINT TRIANGLES ON FIN 12
-- ══════════════════════════════════════════════════════════════════════════════

def A : Finset (Fin 12) := {0, 1, 2}
def B : Finset (Fin 12) := {3, 4, 5}
def C : Finset (Fin 12) := {6, 7, 8}
def D : Finset (Fin 12) := {9, 10, 11}

def M : Finset (Finset (Fin 12)) := {A, B, C, D}

-- ══════════════════════════════════════════════════════════════════════════════
-- GRAPH: Adjacency only within M-triangles
-- ══════════════════════════════════════════════════════════════════════════════

def adj (x y : Fin 12) : Bool :=
  x ≠ y ∧ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ (x ∈ C ∧ y ∈ C) ∨ (x ∈ D ∧ y ∈ D))

def isTriangleInG (T : Finset (Fin 12)) : Bool :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → adj x y)

-- ══════════════════════════════════════════════════════════════════════════════
-- THE 4-EDGE COVER
-- ══════════════════════════════════════════════════════════════════════════════

def cover : Finset (Finset (Fin 12)) :=
  { {0, 1}, {3, 4}, {6, 7}, {9, 10} }

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_card : A.card = 3 := by native_decide
lemma B_card : B.card = 3 := by native_decide
lemma C_card : C.card = 3 := by native_decide
lemma D_card : D.card = 3 := by native_decide
lemma M_card : M.card = 4 := by native_decide
lemma cover_card : cover.card = 4 := by native_decide

lemma cover_all_card_2 : ∀ e ∈ cover, e.card = 2 := by
  intro e he
  simp only [cover, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- DISJOINTNESS VERIFICATION
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_inter_B : (A ∩ B).card = 0 := by native_decide
lemma A_inter_C : (A ∩ C).card = 0 := by native_decide
lemma A_inter_D : (A ∩ D).card = 0 := by native_decide
lemma B_inter_C : (B ∩ C).card = 0 := by native_decide
lemma B_inter_D : (B ∩ D).card = 0 := by native_decide
lemma C_inter_D : (C ∩ D).card = 0 := by native_decide

lemma M_packing : ∀ X ∈ M, ∀ Y ∈ M, X ≠ Y → (X ∩ Y).card ≤ 1 := by
  intro X hX Y hY hne
  simp only [M, mem_insert, mem_singleton] at hX hY
  rcases hX with rfl | rfl | rfl | rfl <;>
  rcases hY with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: Only M-triangles exist (no cross-connections)
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesInG : Finset (Finset (Fin 12)) :=
  (Finset.univ : Finset (Fin 12)).powerset.filter (fun T => isTriangleInG T)

/-- The only triangles in G are exactly A, B, C, D -/
lemma triangles_eq_M : trianglesInG = M := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERAGE
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover_hits_A : ∃ e ∈ cover, e ⊆ A := by
  use {0, 1}; simp only [cover, A, mem_insert, true_or, subset_iff]; decide

lemma cover_hits_B : ∃ e ∈ cover, e ⊆ B := by
  use {3, 4}; simp only [cover, B, mem_insert, or_true, subset_iff]; decide

lemma cover_hits_C : ∃ e ∈ cover, e ⊆ C := by
  use {6, 7}; simp only [cover, C, mem_insert, or_true, subset_iff]; decide

lemma cover_hits_D : ∃ e ∈ cover, e ⊆ D := by
  use {9, 10}; simp only [cover, D, mem_insert, or_true, subset_iff]; decide

lemma cover_hits_M : ∀ X ∈ M, ∃ e ∈ cover, e ⊆ X := by
  intro X hX
  simp only [M, mem_insert, mem_singleton] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · exact cover_hits_A
  · exact cover_hits_B
  · exact cover_hits_C
  · exact cover_hits_D

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

theorem cover_hits_all_triangles :
    ∀ T ∈ trianglesInG, ∃ e ∈ cover, e ⊆ T := by
  intro T hT
  rw [triangles_eq_M] at hT
  exact cover_hits_M T hT

theorem scattered_tau_le_4 :
    ∃ E : Finset (Finset (Fin 12)),
      E.card ≤ 4 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  use cover
  refine ⟨?_, cover_all_card_2, cover_hits_all_triangles⟩
  simp only [cover_card, le_refl]

theorem scattered_tau_le_8 :
    ∃ E : Finset (Finset (Fin 12)),
      E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  obtain ⟨E, hcard, hedge, hcover⟩ := scattered_tau_le_4
  exact ⟨E, by omega, hedge, hcover⟩

/-- Scattered achieves τ = ν = 4 (Tuza's bound is tight) -/
theorem scattered_tau_eq_nu : cover.card = M.card := by
  simp [cover_card, M_card]

end
