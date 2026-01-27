/-
  slot460_classification_v2.lean

  CLASSIFICATION: Bridge vs Private external triangles
  Rewrite of slot456 with more scaffolding for Aristotle.

  TIER: 1 (native_decide on Fin 9)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

namespace ClassificationV2

abbrev V9 := Fin 9

-- DEFINITIONS

def A : Finset V9 := {0, 1, 2}
def B : Finset V9 := {2, 3, 4}
def C : Finset V9 := {4, 5, 6}
def D : Finset V9 := {6, 7, 8}

def M_path4 : Finset (Finset V9) := {A, B, C, D}

def M_edges (M : Finset (Finset V9)) : Finset (Finset V9) :=
  M.biUnion (fun T => T.powersetCard 2)

-- Basic facts
theorem M_path4_card : M_path4.card = 4 := by native_decide
theorem A_card : A.card = 3 := by native_decide
theorem B_card : B.card = 3 := by native_decide
theorem C_card : C.card = 3 := by native_decide
theorem D_card : D.card = 3 := by native_decide

-- M-edges enumeration
theorem M_edges_card : (M_edges M_path4).card = 12 := by native_decide

-- Shared vertex structure
theorem A_inter_B : A ∩ B = {2} := by native_decide
theorem B_inter_C : B ∩ C = {4} := by native_decide
theorem C_inter_D : C ∩ D = {6} := by native_decide
theorem A_inter_C : A ∩ C = ∅ := by native_decide
theorem A_inter_D : A ∩ D = ∅ := by native_decide
theorem B_inter_D : B ∩ D = ∅ := by native_decide

-- Parent counting definition
def getParents (M : Finset (Finset V9)) (T : Finset V9) : Finset (Finset V9) :=
  M.filter (fun X => (X.powersetCard 2 ∩ T.powersetCard 2).Nonempty)

def parentCount (M : Finset (Finset V9)) (T : Finset V9) : ℕ :=
  (getParents M T).card

-- M-elements as their own parent
theorem A_parent_A : A ∈ getParents M_path4 A := by native_decide
theorem B_parent_B : B ∈ getParents M_path4 B := by native_decide
theorem C_parent_C : C ∈ getParents M_path4 C := by native_decide
theorem D_parent_D : D ∈ getParents M_path4 D := by native_decide

theorem A_only_parent : getParents M_path4 A = {A} := by native_decide
theorem B_only_parent : getParents M_path4 B = {B} := by native_decide
theorem C_only_parent : getParents M_path4 C = {C} := by native_decide
theorem D_only_parent : getParents M_path4 D = {D} := by native_decide

theorem M_element_self_parent : ∀ X ∈ M_path4, parentCount M_path4 X = 1 := by
  intro X hX
  fin_cases hX <;> native_decide

-- Bridge T = {3,4,5}
def T_bridge : Finset V9 := {3, 4, 5}

theorem T_bridge_card : T_bridge.card = 3 := by native_decide
theorem T_bridge_not_in_M : T_bridge ∉ M_path4 := by native_decide
theorem T_bridge_parents : getParents M_path4 T_bridge = {B, C} := by native_decide
theorem T_bridge_parent_count : parentCount M_path4 T_bridge = 2 := by native_decide

-- Bridge shares edges with B and C
theorem T_bridge_shares_B : ({3, 4} : Finset V9) ∈ T_bridge.powersetCard 2 ∧ ({3, 4} : Finset V9) ∈ B.powersetCard 2 := by
  native_decide

theorem T_bridge_shares_C : ({4, 5} : Finset V9) ∈ T_bridge.powersetCard 2 ∧ ({4, 5} : Finset V9) ∈ C.powersetCard 2 := by
  native_decide

-- Vertex intersection with bridge
theorem B_inter_bridge : B ∩ T_bridge = {3, 4} := by native_decide
theorem C_inter_bridge : C ∩ T_bridge = {4, 5} := by native_decide
theorem B_inter_bridge_card : (B ∩ T_bridge).card = 2 := by native_decide
theorem C_inter_bridge_card : (C ∩ T_bridge).card = 2 := by native_decide

-- Other potential bridges
def T_AB_bridge : Finset V9 := {1, 2, 3}
def T_CD_bridge : Finset V9 := {5, 6, 7}

theorem T_AB_bridge_parents : getParents M_path4 T_AB_bridge = {A, B} := by native_decide
theorem T_CD_bridge_parents : getParents M_path4 T_CD_bridge = {C, D} := by native_decide

-- Non-adjacent pairs cannot have bridges
-- A and C are vertex-disjoint, so no triangle can share edges with both
theorem no_AC_bridge (T : Finset V9) (hT : T.card = 3) :
    A ∈ getParents M_path4 T → C ∈ getParents M_path4 T → False := by
  intro hA hC
  -- If T shares edge with A, then T ∩ A contains 2 vertices
  -- If T shares edge with C, then T ∩ C contains 2 vertices
  -- But A ∩ C = ∅, so T needs at least 4 distinct vertices
  -- Contradiction with T.card = 3
  native_decide +revert

theorem no_AD_bridge (T : Finset V9) (hT : T.card = 3) :
    A ∈ getParents M_path4 T → D ∈ getParents M_path4 T → False := by
  native_decide +revert

theorem no_BD_bridge (T : Finset V9) (hT : T.card = 3) :
    B ∈ getParents M_path4 T → D ∈ getParents M_path4 T → False := by
  native_decide +revert

-- Bridges only between adjacent pairs
theorem path4_bridges_only_adjacent (T : Finset V9) (hT : T.card = 3) (h2 : parentCount M_path4 T = 2) :
    (getParents M_path4 T = {A, B}) ∨ (getParents M_path4 T = {B, C}) ∨ (getParents M_path4 T = {C, D}) := by
  -- By no_AC_bridge, no_AD_bridge, no_BD_bridge, the only 2-parent sets are adjacent pairs
  native_decide +revert

-- At most 2 parents for any non-M triangle
theorem at_most_two_parents_concrete (T : Finset V9) (hT : T.card = 3) (hNotM : T ∉ M_path4) :
    parentCount M_path4 T ≤ 2 := by
  -- If T had 3 parents, it would share edges with A, B, C (or some triple)
  -- But non-adjacent pairs are blocked by no_AC_bridge etc.
  -- The only way to have 3 parents is if T shares edges with A, B, and C
  -- But then A-B-C are pairwise adjacent in intersection graph, which isn't true for PATH_4
  native_decide +revert

-- Zero parents means edge-disjoint from M
theorem zero_parents_means_disjoint (T : Finset V9) (hT : T.card = 3) (h0 : parentCount M_path4 T = 0) :
    (T.powersetCard 2 ∩ M_edges M_path4) = ∅ := by
  native_decide +revert

-- MAIN CLASSIFICATION THEOREM
theorem classification_complete (T : Finset V9) (hT : T.card = 3) (hNotM : T ∉ M_path4) :
    parentCount M_path4 T = 0 ∨ parentCount M_path4 T = 1 ∨ parentCount M_path4 T = 2 := by
  have h := at_most_two_parents_concrete T hT hNotM
  omega

-- Interactions require bridges
theorem interaction_needs_bridge (e₁ e₂ : Finset V9)
    (he₁ : e₁ ∈ M_edges M_path4) (he₂ : e₂ ∈ M_edges M_path4) (hne : e₁ ≠ e₂)
    (T : Finset V9) (hT : T.card = 3) (he₁T : e₁ ⊆ T) (he₂T : e₂ ⊆ T) (hTnotM : T ∉ M_path4) :
    parentCount M_path4 T = 2 := by
  -- e₁, e₂ are distinct M-edges both contained in T
  -- So T shares edges with the M-elements containing e₁ and e₂
  -- These must be different M-elements (M-elements are edge-disjoint)
  -- So T has at least 2 parents
  -- By at_most_two_parents_concrete, exactly 2
  native_decide +revert

end ClassificationV2
