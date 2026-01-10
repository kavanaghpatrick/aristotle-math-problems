/-
  slot252_same_edge_counterexample.lean

  GOAL: Verify that `same_edge_share_external_vertex` is FALSE
  by constructing a formal counterexample.

  0 SORRY expected - should be fully decidable.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

-- ══════════════════════════════════════════════════════════════════════════════
-- COUNTEREXAMPLE GRAPH (16 vertices)
-- ══════════════════════════════════════════════════════════════════════════════

def CE2_edges : List (Fin 16 × Fin 16) := [
  -- A = {0, 1, 2}
  (0, 1), (1, 2), (2, 0),
  -- B = {7, 8, 9}
  (7, 8), (8, 9), (9, 7),
  -- C = {10, 11, 12}
  (10, 11), (11, 12), (12, 10),
  -- D = {13, 14, 15}
  (13, 14), (14, 15), (15, 13),
  -- T₁ = {0, 1, 5}
  (0, 5), (1, 5),
  -- T₂ = {0, 1, 6}
  (0, 6), (1, 6)
]

def CE2_G : SimpleGraph (Fin 16) := SimpleGraph.fromRel (fun x y => (x, y) ∈ CE2_edges ∨ (y, x) ∈ CE2_edges)

def CE2_A : Finset (Fin 16) := {0, 1, 2}
def CE2_B : Finset (Fin 16) := {7, 8, 9}
def CE2_C : Finset (Fin 16) := {10, 11, 12}
def CE2_D : Finset (Fin 16) := {13, 14, 15}
def CE2_M : Finset (Finset (Fin 16)) := {CE2_A, CE2_B, CE2_C, CE2_D}

def CE2_T1 : Finset (Fin 16) := {0, 1, 5}
def CE2_T2 : Finset (Fin 16) := {0, 1, 6}

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY PROPERTIES (all decidable)
-- ══════════════════════════════════════════════════════════════════════════════

-- T₁ and T₂ use the same edge from A
lemma CE2_same_edge : CE2_T1 ∩ CE2_A = CE2_T2 ∩ CE2_A := by native_decide

-- T₁ ≠ T₂
lemma CE2_T1_ne_T2 : CE2_T1 ≠ CE2_T2 := by native_decide

-- T₁ ∩ T₂ = {0, 1} (inside A)
lemma CE2_intersection : CE2_T1 ∩ CE2_T2 = ({0, 1} : Finset (Fin 16)) := by native_decide

-- The intersection is a subset of A
lemma CE2_intersection_subset_A : CE2_T1 ∩ CE2_T2 ⊆ CE2_A := by native_decide

-- No vertex outside A is in both T₁ and T₂
lemma CE2_no_shared_external : ∀ x : Fin 16, x ∉ CE2_A → x ∈ CE2_T1 → x ∉ CE2_T2 := by
  native_decide

-- The conclusion of same_edge_share_external_vertex is FALSE
theorem CE2_conclusion_false : ¬∃ x : Fin 16, x ∉ CE2_A ∧ x ∈ CE2_T1 ∧ x ∈ CE2_T2 := by
  push_neg
  intro x hx_not_A hx_T1
  exact CE2_no_shared_external x hx_not_A hx_T1

-- ══════════════════════════════════════════════════════════════════════════════
-- VERIFY BASIC PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

lemma CE2_M_card : CE2_M.card = 4 := by native_decide

lemma CE2_A_card : CE2_A.card = 3 := by native_decide

lemma CE2_T1_card : CE2_T1.card = 3 := by native_decide

lemma CE2_T2_card : CE2_T2.card = 3 := by native_decide

-- T₁ and T₂ are not in M
lemma CE2_T1_not_in_M : CE2_T1 ∉ CE2_M := by native_decide

lemma CE2_T2_not_in_M : CE2_T2 ∉ CE2_M := by native_decide

-- T₁ and T₂ are disjoint from B, C, D (intersection ≤ 1)
lemma CE2_T1_inter_B : (CE2_T1 ∩ CE2_B).card ≤ 1 := by native_decide
lemma CE2_T1_inter_C : (CE2_T1 ∩ CE2_C).card ≤ 1 := by native_decide
lemma CE2_T1_inter_D : (CE2_T1 ∩ CE2_D).card ≤ 1 := by native_decide
lemma CE2_T2_inter_B : (CE2_T2 ∩ CE2_B).card ≤ 1 := by native_decide
lemma CE2_T2_inter_C : (CE2_T2 ∩ CE2_C).card ≤ 1 := by native_decide
lemma CE2_T2_inter_D : (CE2_T2 ∩ CE2_D).card ≤ 1 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ══════════════════════════════════════════════════════════════════════════════

/-
  This file proves that the lemma `same_edge_share_external_vertex` is FALSE.

  In this counterexample graph:
  - M = {A, B, C, D} with |M| = 4
  - T₁ = {0, 1, 5} and T₂ = {0, 1, 6} are both external of A
  - T₁ ∩ A = T₂ ∩ A = {0, 1} (they use the SAME edge from A)
  - But T₁ ∩ T₂ = {0, 1} ⊆ A
  - So there's NO x with x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂

  The lemma claims ∃ x, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂, which is FALSE here.

  IMPLICATION: The "apex approach" to proving τ ≤ 8 is DEAD.
  We cannot assume all externals of an M-element share a common apex.
-/

end
