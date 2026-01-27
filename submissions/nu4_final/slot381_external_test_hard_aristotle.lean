/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 58a5cdd0-5f81-432e-9330-bbcde7c5cd69
-/

/-
Tuza ν=4 Strategy - Slot 381: External Test (HARD MODE)

THIS IS THE KEY TEST: Graph with actual external triangles.

DEBATE CONSENSUS LEMMA:
  If T is external for e (shares vertex but not edge with e),
  then T must share edge with some f ∈ M, f ≠ e.

TEST SETUP (PATH_4 with extra edges creating externals):
  M = {A, B, C, D} where:
  A = {0, 1, 2}     -- vertex 2 shared with B
  B = {2, 3, 4}     -- vertex 4 shared with C
  C = {4, 5, 6}     -- vertex 6 shared with D
  D = {6, 7, 0}     -- vertex 0 shared with A (cycle closure)

  EXTRA EDGES added to create external triangles:
  - Edge {1, 3}: Creates triangle {1, 2, 3} which:
      * Shares vertex 2 with A but not edge (external for A)
      * Shares edge {2,3} with B (in S_B)
  - Edge {3, 5}: Creates triangle {3, 4, 5} which:
      * Shares vertex 4 with B but not edge (external for B)
      * Shares edge {4,5} with C (in S_C)

KEY TEST: Does every external have an S_f home?

TIER: 1-2 (Decidable on Fin 8 with ~60 triangles to check)
-/

import Mathlib


set_option maxHeartbeats 1600000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING M ON FIN 8 (PATH_4 / CYCLE_4 configuration)
-- ══════════════════════════════════════════════════════════════════════════════

def A : Finset (Fin 8) := {0, 1, 2}

def B : Finset (Fin 8) := {2, 3, 4}

def C : Finset (Fin 8) := {4, 5, 6}

def D : Finset (Fin 8) := {6, 7, 0}

def M : Finset (Finset (Fin 8)) := {A, B, C, D}

-- ══════════════════════════════════════════════════════════════════════════════
-- GRAPH WITH EXTRA EDGES (creates externals!)
-- ══════════════════════════════════════════════════════════════════════════════

-- All edges: M-triangle edges + extra edges
def allEdges : Finset (Finset (Fin 8)) :=
  -- A edges
  { {0, 1}, {0, 2}, {1, 2},
  -- B edges
    {2, 3}, {2, 4}, {3, 4},
  -- C edges
    {4, 5}, {4, 6}, {5, 6},
  -- D edges
    {6, 7}, {6, 0}, {7, 0},
  -- EXTRA EDGES that create external triangles
    {1, 3},   -- Creates external {1,2,3} for A (but in S_B)
    {3, 5},   -- Creates external {3,4,5} for B (but in S_C)
    {5, 7},   -- Creates external {5,6,7} for C (but in S_D)
    {7, 1} }

-- Creates external {7,0,1} for D (but in S_A)

-- Adjacency in the extended graph
def adj (x y : Fin 8) : Bool :=
  x ≠ y ∧ ({x, y} : Finset (Fin 8)) ∈ allEdges

def isTriangleInG (T : Finset (Fin 8)) : Bool :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → adj x y)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def triangleEdges (T : Finset (Fin 8)) : Finset (Finset (Fin 8)) :=
  T.powerset.filter (fun e => e.card = 2)

def packingEdges (e : Finset (Fin 8)) : Finset (Finset (Fin 8)) :=
  e.powerset.filter (fun edge => edge.card = 2)

def sharesEdgeWith (T e : Finset (Fin 8)) : Bool :=
  (triangleEdges T ∩ packingEdges e).Nonempty

def sharesOnlyVertex (T e : Finset (Fin 8)) : Bool :=
  (T ∩ e).Nonempty ∧ ¬sharesEdgeWith T e

def isExternalFor (T e : Finset (Fin 8)) : Bool :=
  sharesOnlyVertex T e

-- S_e: triangles sharing edge with e
def trianglesSharingEdge (e : Finset (Fin 8)) : Finset (Finset (Fin 8)) :=
  (Finset.univ : Finset (Fin 8)).powerset.filter (fun T =>
    isTriangleInG T ∧ sharesEdgeWith T e)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_card : A.card = 3 := by native_decide

lemma B_card : B.card = 3 := by native_decide

lemma C_card : C.card = 3 := by native_decide

lemma D_card : D.card = 3 := by native_decide

lemma M_card : M.card = 4 := by native_decide

lemma A_in_M : A ∈ M := by native_decide

lemma B_in_M : B ∈ M := by native_decide

lemma C_in_M : C ∈ M := by native_decide

lemma D_in_M : D ∈ M := by native_decide

lemma M_packing : ∀ X ∈ M, ∀ Y ∈ M, X ≠ Y → (X ∩ Y).card ≤ 1 := by
  intro X hX Y hY hne
  simp only [M, mem_insert, mem_singleton] at hX hY
  rcases hX with rfl | rfl | rfl | rfl <;>
  rcases hY with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- ENUMERATE TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesInG : Finset (Finset (Fin 8)) :=
  (Finset.univ : Finset (Fin 8)).powerset.filter (fun T => isTriangleInG T)

/-- The triangles in this graph: 4 M-triangles + 4 external triangles -/
lemma triangles_enumeration : trianglesInG =
    {A, B, C, D,
     {1, 2, 3},   -- external for A, shares edge {2,3} with B
     {3, 4, 5},   -- external for B, shares edge {4,5} with C
     {5, 6, 7},   -- external for C, shares edge {6,7} with D
     {7, 0, 1}}   -- external for D, shares edge {0,1} with A
    := by native_decide

lemma triangles_card : trianglesInG.card = 8 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- VERIFY: External {1,2,3} is external for A but shares edge with B
-- ══════════════════════════════════════════════════════════════════════════════

def ext1 : Finset (Fin 8) := {1, 2, 3}

lemma ext1_is_triangle : ext1 ∈ trianglesInG := by native_decide

lemma ext1_external_for_A : isExternalFor ext1 A = true := by native_decide

lemma ext1_shares_edge_with_B : sharesEdgeWith ext1 B = true := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- VERIFY: External {3,4,5} is external for B but shares edge with C
-- ══════════════════════════════════════════════════════════════════════════════

def ext2 : Finset (Fin 8) := {3, 4, 5}

lemma ext2_is_triangle : ext2 ∈ trianglesInG := by native_decide

lemma ext2_external_for_B : isExternalFor ext2 B = true := by native_decide

lemma ext2_shares_edge_with_C : sharesEdgeWith ext2 C = true := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- THE KEY THEOREM: Every triangle shares edge with some M-element
-- ══════════════════════════════════════════════════════════════════════════════

/--
PROOF SKETCH:
Every triangle T in G shares edge with some e ∈ M.
This is the maximality property that makes the whole approach work.
In this graph with 8 triangles, we can verify exhaustively.
-/
theorem every_triangle_shares_edge_with_M :
    ∀ T ∈ trianglesInG, ∃ e ∈ M, sharesEdgeWith T e = true := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- THE KEY COROLLARY: Externals have homes in other S_f
-- ══════════════════════════════════════════════════════════════════════════════

/--
If T is external for e (shares vertex but not edge), then
T shares edge with some OTHER element f ∈ M.
This is the debate consensus insight!
-/
theorem external_has_other_home :
    ∀ T ∈ trianglesInG, ∀ e ∈ M,
      isExternalFor T e = true →
      ∃ f ∈ M, f ≠ e ∧ sharesEdgeWith T f = true := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- EXPLICIT 8-EDGE COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-
Cover strategy (from debate):
Each S_e needs ≤ 2 edges. Since every triangle is in some S_e,
we use 4 × 2 = 8 edges total.

For this specific graph:
  - S_A triangles: A, {7,0,1} → cover with {0,1}, {0,2} (2 edges)
  - S_B triangles: B, {1,2,3} → cover with {2,3}, {3,4} (2 edges)
  - S_C triangles: C, {3,4,5} → cover with {4,5}, {5,6} (2 edges)
  - S_D triangles: D, {5,6,7} → cover with {6,7}, {7,0} (2 edges)
-/

def cover : Finset (Finset (Fin 8)) :=
  { {0, 1}, {0, 2},   -- covers S_A
    {2, 3}, {3, 4},   -- covers S_B
    {4, 5}, {5, 6},   -- covers S_C
    {6, 7}, {7, 0} }

-- covers S_D

lemma cover_card : cover.card = 8 := by native_decide

lemma cover_all_card_2 : ∀ e ∈ cover, e.card = 2 := by
  intro e he
  simp only [cover, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/--
PROOF SKETCH (debate consensus):
1. Every triangle T shares edge with some e ∈ M (maximality)
2. T ∈ S_e for that e
3. S_e can be covered by ≤ 2 edges
4. 4 elements × 2 edges = 8 edges total
-/
theorem tau_le_8_hard_mode :
    ∃ E : Finset (Finset (Fin 8)),
      E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  use cover
  refine ⟨?_, cover_all_card_2, ?_⟩
  · simp only [cover_card, le_refl]
  · -- Every triangle is covered by some edge in cover
    native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL INSIGHT: S_e partition (with overlap for bridges)
-- ══════════════════════════════════════════════════════════════════════════════

/-- S_A = triangles sharing edge with A = {A, ext4} where ext4 = {7,0,1} -/
lemma S_A_members : trianglesSharingEdge A = {A, {7, 0, 1}} := by native_decide

/-- S_B = triangles sharing edge with B = {B, ext1} where ext1 = {1,2,3} -/
lemma S_B_members : trianglesSharingEdge B = {B, {1, 2, 3}} := by native_decide

/-- S_C = triangles sharing edge with C = {C, ext2} where ext2 = {3,4,5} -/
lemma S_C_members : trianglesSharingEdge C = {C, {3, 4, 5}} := by native_decide

/-- S_D = triangles sharing edge with D = {D, ext3} where ext3 = {5,6,7} -/
lemma S_D_members : trianglesSharingEdge D = {D, {5, 6, 7}} := by native_decide

/-- All triangles are covered by S_A ∪ S_B ∪ S_C ∪ S_D -/
lemma all_triangles_in_union_S :
    trianglesInG ⊆ trianglesSharingEdge A ∪ trianglesSharingEdge B ∪
                   trianglesSharingEdge C ∪ trianglesSharingEdge D := by
  native_decide

/-- Each S_e has size ≤ 2 (in this graph) -/
lemma S_A_card : (trianglesSharingEdge A).card = 2 := by native_decide

lemma S_B_card : (trianglesSharingEdge B).card = 2 := by native_decide

lemma S_C_card : (trianglesSharingEdge C).card = 2 := by native_decide

lemma S_D_card : (trianglesSharingEdge D).card = 2 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- VERIFICATION: No bridges in this graph (clean S_e decomposition)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle is a bridge if it shares edges with TWO different M-elements -/
def isBridge (T : Finset (Fin 8)) : Bool :=
  ∃ e ∈ M, ∃ f ∈ M, e ≠ f ∧ sharesEdgeWith T e ∧ sharesEdgeWith T f

/-- In this graph, there are no bridge triangles -/
lemma no_bridges : ∀ T ∈ trianglesInG, isBridge T = false := by
  native_decide

end