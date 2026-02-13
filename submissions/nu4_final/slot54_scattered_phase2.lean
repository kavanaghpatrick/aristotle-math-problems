/-
Tuza ν=4: SCATTERED Phase 2 - General Graph with Externals
Slot 54

CASE DESCRIPTION:
  4 completely disjoint M-triangles (no shared vertices).
  PLUS: External triangles that share exactly one edge with one M-element.

STRUCTURE (on Fin 15):
  A = {0, 1, 2}
  B = {3, 4, 5}
  C = {6, 7, 8}
  D = {9, 10, 11}
  Extra vertices: 12, 13, 14 (for externals)

GRAPH CONSTRUCTION:
  - All edges within each M-triangle
  - External triangle E1 = {0, 1, 12} shares edge {0,1} with A
  - External triangle E2 = {3, 4, 13} shares edge {3,4} with B
  - External triangle E3 = {6, 7, 14} shares edge {6,7} with C
  (No external for D - tests asymmetry)

KEY INSIGHT (from debate):
  In scattered, M-elements are PAIRWISE VERTEX-DISJOINT.
  Therefore each external shares edge with exactly ONE M-element.
  No bridges exist (bridges require sharing with TWO M-elements).
  S_e partition is clean: S_{0,1} = {E1}, S_{3,4} = {E2}, S_{6,7} = {E3}.

COVER CONSTRUCTION (8 edges):
  For M-elements: One edge each = 4 edges
    {0,1}, {3,4}, {6,7}, {9,10}
  But externals share these edges! So no extra edges needed.

  Actually τ ≤ 4 still works if externals share M-edges.

PROOF SKETCH:
1. Define graph G with M-triangles + externals
2. Each external shares an edge with exactly one M-element
3. The 4-edge cover from M-edges covers all externals too
4. Therefore τ ≤ 4 (even with externals!)

TIER: 1 (Decidable on Fin 15 via native_decide)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

namespace ScatteredPhase2

abbrev V := Fin 15

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: M-Triangle Definitions
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangle A: first group -/
def A : Finset V := {0, 1, 2}

/-- Triangle B: second group -/
def B : Finset V := {3, 4, 5}

/-- Triangle C: third group -/
def C : Finset V := {6, 7, 8}

/-- Triangle D: fourth group -/
def D : Finset V := {9, 10, 11}

/-- The maximal packing M = {A, B, C, D} -/
def M : Finset (Finset V) := {A, B, C, D}

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: External Triangle Definitions
-- ══════════════════════════════════════════════════════════════════════════════

/-- External E1: shares edge {0,1} with A -/
def E1 : Finset V := {0, 1, 12}

/-- External E2: shares edge {3,4} with B -/
def E2 : Finset V := {3, 4, 13}

/-- External E3: shares edge {6,7} with C -/
def E3 : Finset V := {6, 7, 14}

/-- All externals -/
def externals : Finset (Finset V) := {E1, E2, E3}

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: Graph Definition
-- ══════════════════════════════════════════════════════════════════════════════

/-- Adjacency: distinct vertices in same triangle (M or external) -/
def scatteredAdj (x y : V) : Prop :=
  x ≠ y ∧ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ (x ∈ C ∧ y ∈ C) ∨ (x ∈ D ∧ y ∈ D) ∨
           (x ∈ E1 ∧ y ∈ E1) ∨ (x ∈ E2 ∧ y ∈ E2) ∨ (x ∈ E3 ∧ y ∈ E3))

instance : DecidableRel scatteredAdj := fun x y => by
  unfold scatteredAdj
  infer_instance

/-- The scattered graph G with externals -/
def G : SimpleGraph V where
  Adj := scatteredAdj
  symm := by intro x y ⟨hne, h⟩; exact ⟨hne.symm, by tauto⟩
  loopless := by intro x ⟨hne, _⟩; exact hne rfl

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel scatteredAdj)

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: Triangle Detection
-- ══════════════════════════════════════════════════════════════════════════════

/-- A set is a clique in G -/
def isCliqueInG (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y

instance (s : Finset V) : Decidable (isCliqueInG s) := by
  unfold isCliqueInG; infer_instance

/-- A set is a triangle in G -/
def isTriangleInG (T : Finset V) : Prop :=
  T.card = 3 ∧ isCliqueInG T

instance (T : Finset V) : Decidable (isTriangleInG T) := by
  unfold isTriangleInG; infer_instance

/-- All triangles in G -/
def trianglesInG : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter isTriangleInG

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: Scaffolding Lemmas (10+ helpers)
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_card : A.card = 3 := by native_decide
lemma B_card : B.card = 3 := by native_decide
lemma C_card : C.card = 3 := by native_decide
lemma D_card : D.card = 3 := by native_decide
lemma M_card : M.card = 4 := by native_decide

lemma E1_card : E1.card = 3 := by native_decide
lemma E2_card : E2.card = 3 := by native_decide
lemma E3_card : E3.card = 3 := by native_decide

/-- M-triangles are pairwise vertex-disjoint -/
lemma A_inter_B : (A ∩ B).card = 0 := by native_decide
lemma A_inter_C : (A ∩ C).card = 0 := by native_decide
lemma A_inter_D : (A ∩ D).card = 0 := by native_decide
lemma B_inter_C : (B ∩ C).card = 0 := by native_decide
lemma B_inter_D : (B ∩ D).card = 0 := by native_decide
lemma C_inter_D : (C ∩ D).card = 0 := by native_decide

/-- E1 shares edge with A (2 vertices) -/
lemma E1_inter_A : (E1 ∩ A).card = 2 := by native_decide

/-- E1 shares nothing with B, C, D -/
lemma E1_inter_B : (E1 ∩ B).card = 0 := by native_decide
lemma E1_inter_C : (E1 ∩ C).card = 0 := by native_decide
lemma E1_inter_D : (E1 ∩ D).card = 0 := by native_decide

/-- E2 shares edge with B only -/
lemma E2_inter_A : (E2 ∩ A).card = 0 := by native_decide
lemma E2_inter_B : (E2 ∩ B).card = 2 := by native_decide
lemma E2_inter_C : (E2 ∩ C).card = 0 := by native_decide
lemma E2_inter_D : (E2 ∩ D).card = 0 := by native_decide

/-- E3 shares edge with C only -/
lemma E3_inter_A : (E3 ∩ A).card = 0 := by native_decide
lemma E3_inter_B : (E3 ∩ B).card = 0 := by native_decide
lemma E3_inter_C : (E3 ∩ C).card = 2 := by native_decide
lemma E3_inter_D : (E3 ∩ D).card = 0 := by native_decide

/-- M is a valid packing (pairwise edge-disjoint) -/
lemma M_packing : ∀ X ∈ M, ∀ Y ∈ M, X ≠ Y → (X ∩ Y).card ≤ 1 := by
  intro X hX Y hY hne
  simp only [M, mem_insert, mem_singleton] at hX hY
  rcases hX with rfl | rfl | rfl | rfl <;>
  rcases hY with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: Clique Verification
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_is_clique : isCliqueInG A := by native_decide
lemma B_is_clique : isCliqueInG B := by native_decide
lemma C_is_clique : isCliqueInG C := by native_decide
lemma D_is_clique : isCliqueInG D := by native_decide
lemma E1_is_clique : isCliqueInG E1 := by native_decide
lemma E2_is_clique : isCliqueInG E2 := by native_decide
lemma E3_is_clique : isCliqueInG E3 := by native_decide

lemma A_is_triangle : isTriangleInG A := ⟨A_card, A_is_clique⟩
lemma B_is_triangle : isTriangleInG B := ⟨B_card, B_is_clique⟩
lemma C_is_triangle : isTriangleInG C := ⟨C_card, C_is_clique⟩
lemma D_is_triangle : isTriangleInG D := ⟨D_card, D_is_clique⟩
lemma E1_is_triangle : isTriangleInG E1 := ⟨E1_card, E1_is_clique⟩
lemma E2_is_triangle : isTriangleInG E2 := ⟨E2_card, E2_is_clique⟩
lemma E3_is_triangle : isTriangleInG E3 := ⟨E3_card, E3_is_clique⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 7: Triangle Enumeration
-- ══════════════════════════════════════════════════════════════════════════════

/-- The triangles in G are exactly M ∪ externals -/
lemma triangles_eq : trianglesInG = M ∪ externals := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 8: Cover Construction
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 4-edge cover: one edge from each M-triangle -/
def cover : Finset (Finset V) :=
  { {0, 1},   -- covers A AND E1
    {3, 4},   -- covers B AND E2
    {6, 7},   -- covers C AND E3
    {9, 10} } -- covers D

lemma cover_card : cover.card = 4 := by native_decide

lemma cover_all_edges : ∀ e ∈ cover, e.card = 2 := by
  intro e he
  simp only [cover, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 9: Coverage Verification
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_01_in_A : {(0 : V), 1} ⊆ A := by native_decide
lemma edge_34_in_B : {(3 : V), 4} ⊆ B := by native_decide
lemma edge_67_in_C : {(6 : V), 7} ⊆ C := by native_decide
lemma edge_910_in_D : {(9 : V), 10} ⊆ D := by native_decide

lemma edge_01_in_E1 : {(0 : V), 1} ⊆ E1 := by native_decide
lemma edge_34_in_E2 : {(3 : V), 4} ⊆ E2 := by native_decide
lemma edge_67_in_E3 : {(6 : V), 7} ⊆ E3 := by native_decide

lemma cover_hits_A : ∃ e ∈ cover, e ⊆ A := ⟨{0, 1}, by native_decide, edge_01_in_A⟩
lemma cover_hits_B : ∃ e ∈ cover, e ⊆ B := ⟨{3, 4}, by native_decide, edge_34_in_B⟩
lemma cover_hits_C : ∃ e ∈ cover, e ⊆ C := ⟨{6, 7}, by native_decide, edge_67_in_C⟩
lemma cover_hits_D : ∃ e ∈ cover, e ⊆ D := ⟨{9, 10}, by native_decide, edge_910_in_D⟩

lemma cover_hits_E1 : ∃ e ∈ cover, e ⊆ E1 := ⟨{0, 1}, by native_decide, edge_01_in_E1⟩
lemma cover_hits_E2 : ∃ e ∈ cover, e ⊆ E2 := ⟨{3, 4}, by native_decide, edge_34_in_E2⟩
lemma cover_hits_E3 : ∃ e ∈ cover, e ⊆ E3 := ⟨{6, 7}, by native_decide, edge_67_in_E3⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 10: Main Theorems
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for cover_hits_all_triangles:
1. By triangles_eq, all triangles are in M ∪ externals
2. For M-triangles: cover edges hit each (A,B,C,D)
3. For externals: E1 shares edge {0,1} with A, E2 shares {3,4} with B, E3 shares {6,7} with C
4. Same cover edges hit both M and externals
5. Therefore cover hits all triangles
-/

/-- Cover hits all triangles in G -/
theorem cover_hits_all_triangles : ∀ T ∈ trianglesInG, ∃ e ∈ cover, e ⊆ T := by
  intro T hT
  rw [triangles_eq] at hT
  simp only [M, externals, mem_union, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cover_hits_A
  · exact cover_hits_B
  · exact cover_hits_C
  · exact cover_hits_D
  · exact cover_hits_E1
  · exact cover_hits_E2
  · exact cover_hits_E3

/-
PROOF SKETCH for scattered_phase2_tau_le_4:
1. Cover has 4 edges
2. Each edge has exactly 2 vertices (valid edge)
3. Cover hits all triangles (by cover_hits_all_triangles)
4. Therefore τ ≤ 4
-/

/-- SCATTERED Phase 2: τ ≤ 4 even with externals -/
theorem scattered_phase2_tau_le_4 :
    ∃ E : Finset (Finset V),
      E.card ≤ 4 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  use cover
  refine ⟨?_, cover_all_edges, cover_hits_all_triangles⟩
  simp only [cover_card, le_refl]

/-- Corollary: τ ≤ 8 (Tuza's bound τ ≤ 2ν with ν = 4) -/
theorem scattered_phase2_tau_le_8 :
    ∃ E : Finset (Finset V),
      E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  obtain ⟨E, hcard, hedge, hcover⟩ := scattered_phase2_tau_le_4
  exact ⟨E, by omega, hedge, hcover⟩

/-- The packing is valid (4 edge-disjoint triangles) -/
theorem packing_is_valid : M.card = 4 ∧ ∀ T ∈ M, isTriangleInG T := by
  constructor
  · exact M_card
  · intro T hT
    simp only [M, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact A_is_triangle
    · exact B_is_triangle
    · exact C_is_triangle
    · exact D_is_triangle

/-- Key property: No bridges exist in scattered -/
theorem no_bridges_in_scattered :
    ∀ T ∈ externals, ∃! X, X ∈ M ∧ (T ∩ X).card = 2 := by
  intro T hT
  simp only [externals, M, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  -- E1 shares edge only with A
  · use A
    simp only [mem_insert, mem_singleton, true_or, and_true]
    constructor
    · native_decide
    · intro Y ⟨hYM, hYinter⟩
      simp only [mem_insert, mem_singleton] at hYM
      rcases hYM with rfl | rfl | rfl | rfl
      · rfl
      · simp only [E1_inter_B] at hYinter; omega
      · simp only [E1_inter_C] at hYinter; omega
      · simp only [E1_inter_D] at hYinter; omega
  -- E2 shares edge only with B
  · use B
    simp only [mem_insert, mem_singleton, or_true, true_or, and_true]
    constructor
    · native_decide
    · intro Y ⟨hYM, hYinter⟩
      simp only [mem_insert, mem_singleton] at hYM
      rcases hYM with rfl | rfl | rfl | rfl
      · simp only [E2_inter_A] at hYinter; omega
      · rfl
      · simp only [E2_inter_C] at hYinter; omega
      · simp only [E2_inter_D] at hYinter; omega
  -- E3 shares edge only with C
  · use C
    simp only [mem_insert, mem_singleton, or_true, and_true]
    constructor
    · native_decide
    · intro Y ⟨hYM, hYinter⟩
      simp only [mem_insert, mem_singleton] at hYM
      rcases hYM with rfl | rfl | rfl | rfl
      · simp only [E3_inter_A] at hYinter; omega
      · simp only [E3_inter_B] at hYinter; omega
      · rfl
      · simp only [E3_inter_D] at hYinter; omega

/-- Summary: Scattered with externals achieves τ = ν = 4 -/
theorem scattered_summary :
    M.card = 4 ∧
    trianglesInG.card = 7 ∧  -- 4 M-triangles + 3 externals
    cover.card = 4 ∧
    (∀ T ∈ trianglesInG, ∃ e ∈ cover, e ⊆ T) := by
  refine ⟨M_card, ?_, cover_card, cover_hits_all_triangles⟩
  rw [triangles_eq]
  native_decide

end ScatteredPhase2
