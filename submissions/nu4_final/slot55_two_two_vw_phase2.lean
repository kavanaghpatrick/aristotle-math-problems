/-
Tuza ν=4: TWO_TWO_VW Phase 2 - General Graph with Externals
Slot 55

CASE DESCRIPTION:
  4 M-triangles forming 2 disjoint pairs:
  - A and B share vertex v = 0
  - C and D share vertex w = 5
  - Pairs {A,B} and {C,D} are VERTEX-DISJOINT (no shared vertices)
  PLUS: External triangles and potential bridges

STRUCTURE (on Fin 14):
  v = 0 (shared by A, B)
  w = 5 (shared by C, D)

  A = {0, 1, 2}  -- contains v
  B = {0, 3, 4}  -- contains v
  C = {5, 6, 7}  -- contains w
  D = {5, 8, 9}  -- contains w

  Extra vertices: 10, 11, 12, 13 (for externals)

GRAPH CONSTRUCTION:
  - All edges within each M-triangle
  - External E1 = {1, 2, 10} shares base edge {1,2} of A
  - External E2 = {3, 4, 11} shares base edge {3,4} of B
  - External E3 = {6, 7, 12} shares base edge {6,7} of C
  - External E4 = {8, 9, 13} shares base edge {8,9} of D

KEY INSIGHT (from debate):
  Pairs {A,B} and {C,D} are VERTEX-DISJOINT.
  Therefore NO inter-pair bridges can exist:
  - A bridge would need to share edges with BOTH an {A,B} element AND a {C,D} element
  - But {A,B} vertices are {0,1,2,3,4} and {C,D} vertices are {5,6,7,8,9}
  - No triangle can contain vertices from both sets (graph is disconnected there)

  Each external shares exactly ONE edge with ONE M-element.
  τ_pair(A,B) + τ_pair(C,D) = τ(T_pair(A,B)) + τ(T_pair(C,D)) ≤ 4 + 4 = 8

COVER CONSTRUCTION (8 edges):
  For pair {A,B}: 4 spokes from v=0: {0,1}, {0,2}, {0,3}, {0,4}
  For pair {C,D}: 4 spokes from w=5: {5,6}, {5,7}, {5,8}, {5,9}
  Total: 8 edges

  But we can do better with base edges:
  Cover for {A,B}: {0,1} (hits A), {0,3} (hits B), {1,2} (hits E1), {3,4} (hits E2)
  Actually: spoke {0,1} hits A and externals containing 0,1
  Let's use: {0,1}, {0,3}, {1,2}, {3,4}, {5,6}, {5,8}, {6,7}, {8,9} = 8 edges

PROOF SKETCH:
1. Define graph G with M-triangles + externals
2. Pairs are vertex-disjoint: no inter-pair bridges
3. Each pair contributes at most 4 edges to cover
4. Total: τ ≤ 8

TIER: 1 (Decidable on Fin 14 via native_decide)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

namespace TwoTwoVWPhase2

abbrev V := Fin 14

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: Shared Vertices
-- ══════════════════════════════════════════════════════════════════════════════

/-- Shared vertex for pair {A, B} -/
def v : V := 0

/-- Shared vertex for pair {C, D} -/
def w : V := 5

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: M-Triangle Definitions
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangle A: first of pair 1, contains v -/
def A : Finset V := {0, 1, 2}

/-- Triangle B: second of pair 1, contains v -/
def B : Finset V := {0, 3, 4}

/-- Triangle C: first of pair 2, contains w -/
def C : Finset V := {5, 6, 7}

/-- Triangle D: second of pair 2, contains w -/
def D : Finset V := {5, 8, 9}

/-- The maximal packing M = {A, B, C, D} -/
def M : Finset (Finset V) := {A, B, C, D}

/-- Vertices of pair 1: {A, B} -/
def pair1_vertices : Finset V := {0, 1, 2, 3, 4}

/-- Vertices of pair 2: {C, D} -/
def pair2_vertices : Finset V := {5, 6, 7, 8, 9}

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: External Triangle Definitions
-- ══════════════════════════════════════════════════════════════════════════════

/-- External E1: shares base edge {1,2} with A -/
def E1 : Finset V := {1, 2, 10}

/-- External E2: shares base edge {3,4} with B -/
def E2 : Finset V := {3, 4, 11}

/-- External E3: shares base edge {6,7} with C -/
def E3 : Finset V := {6, 7, 12}

/-- External E4: shares base edge {8,9} with D -/
def E4 : Finset V := {8, 9, 13}

/-- All externals -/
def externals : Finset (Finset V) := {E1, E2, E3, E4}

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: Graph Definition
-- ══════════════════════════════════════════════════════════════════════════════

/-- Adjacency: distinct vertices in same triangle (M or external) -/
def twoTwoAdj (x y : V) : Prop :=
  x ≠ y ∧ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ (x ∈ C ∧ y ∈ C) ∨ (x ∈ D ∧ y ∈ D) ∨
           (x ∈ E1 ∧ y ∈ E1) ∨ (x ∈ E2 ∧ y ∈ E2) ∨ (x ∈ E3 ∧ y ∈ E3) ∨ (x ∈ E4 ∧ y ∈ E4))

instance : DecidableRel twoTwoAdj := fun x y => by
  unfold twoTwoAdj
  infer_instance

/-- The two_two_vw graph G with externals -/
def G : SimpleGraph V where
  Adj := twoTwoAdj
  symm := by intro x y ⟨hne, h⟩; exact ⟨hne.symm, by tauto⟩
  loopless := by intro x ⟨hne, _⟩; exact hne rfl

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel twoTwoAdj)

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: Triangle Detection
-- ══════════════════════════════════════════════════════════════════════════════

def isCliqueInG (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y

instance (s : Finset V) : Decidable (isCliqueInG s) := by
  unfold isCliqueInG; infer_instance

def isTriangleInG (T : Finset V) : Prop :=
  T.card = 3 ∧ isCliqueInG T

instance (T : Finset V) : Decidable (isTriangleInG T) := by
  unfold isTriangleInG; infer_instance

def trianglesInG : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter isTriangleInG

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: Scaffolding Lemmas (10+ helpers)
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_card : A.card = 3 := by native_decide
lemma B_card : B.card = 3 := by native_decide
lemma C_card : C.card = 3 := by native_decide
lemma D_card : D.card = 3 := by native_decide
lemma M_card : M.card = 4 := by native_decide

lemma E1_card : E1.card = 3 := by native_decide
lemma E2_card : E2.card = 3 := by native_decide
lemma E3_card : E3.card = 3 := by native_decide
lemma E4_card : E4.card = 3 := by native_decide

/-- v is in A and B -/
lemma v_in_A : v ∈ A := by native_decide
lemma v_in_B : v ∈ B := by native_decide

/-- w is in C and D -/
lemma w_in_C : w ∈ C := by native_decide
lemma w_in_D : w ∈ D := by native_decide

/-- A and B share exactly v -/
lemma A_inter_B : (A ∩ B).card = 1 := by native_decide
lemma A_inter_B_eq : A ∩ B = {v} := by native_decide

/-- C and D share exactly w -/
lemma C_inter_D : (C ∩ D).card = 1 := by native_decide
lemma C_inter_D_eq : C ∩ D = {w} := by native_decide

/-- Pairs are vertex-disjoint (KEY PROPERTY!) -/
lemma A_inter_C : (A ∩ C).card = 0 := by native_decide
lemma A_inter_D : (A ∩ D).card = 0 := by native_decide
lemma B_inter_C : (B ∩ C).card = 0 := by native_decide
lemma B_inter_D : (B ∩ D).card = 0 := by native_decide

/-- Pair vertices are disjoint -/
lemma pairs_disjoint : (pair1_vertices ∩ pair2_vertices).card = 0 := by native_decide

/-- M is a valid packing -/
lemma M_packing : ∀ X ∈ M, ∀ Y ∈ M, X ≠ Y → (X ∩ Y).card ≤ 1 := by
  intro X hX Y hY hne
  simp only [M, mem_insert, mem_singleton] at hX hY
  rcases hX with rfl | rfl | rfl | rfl <;>
  rcases hY with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | native_decide

/-- Externals share edges with M-elements -/
lemma E1_inter_A : (E1 ∩ A).card = 2 := by native_decide
lemma E2_inter_B : (E2 ∩ B).card = 2 := by native_decide
lemma E3_inter_C : (E3 ∩ C).card = 2 := by native_decide
lemma E4_inter_D : (E4 ∩ D).card = 2 := by native_decide

/-- Externals share nothing with other M-elements -/
lemma E1_inter_B : (E1 ∩ B).card = 0 := by native_decide
lemma E1_inter_C : (E1 ∩ C).card = 0 := by native_decide
lemma E1_inter_D : (E1 ∩ D).card = 0 := by native_decide

lemma E2_inter_A : (E2 ∩ A).card = 0 := by native_decide
lemma E2_inter_C : (E2 ∩ C).card = 0 := by native_decide
lemma E2_inter_D : (E2 ∩ D).card = 0 := by native_decide

lemma E3_inter_A : (E3 ∩ A).card = 0 := by native_decide
lemma E3_inter_B : (E3 ∩ B).card = 0 := by native_decide
lemma E3_inter_D : (E3 ∩ D).card = 0 := by native_decide

lemma E4_inter_A : (E4 ∩ A).card = 0 := by native_decide
lemma E4_inter_B : (E4 ∩ B).card = 0 := by native_decide
lemma E4_inter_C : (E4 ∩ C).card = 0 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 7: Clique Verification
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_is_clique : isCliqueInG A := by native_decide
lemma B_is_clique : isCliqueInG B := by native_decide
lemma C_is_clique : isCliqueInG C := by native_decide
lemma D_is_clique : isCliqueInG D := by native_decide
lemma E1_is_clique : isCliqueInG E1 := by native_decide
lemma E2_is_clique : isCliqueInG E2 := by native_decide
lemma E3_is_clique : isCliqueInG E3 := by native_decide
lemma E4_is_clique : isCliqueInG E4 := by native_decide

lemma A_is_triangle : isTriangleInG A := ⟨A_card, A_is_clique⟩
lemma B_is_triangle : isTriangleInG B := ⟨B_card, B_is_clique⟩
lemma C_is_triangle : isTriangleInG C := ⟨C_card, C_is_clique⟩
lemma D_is_triangle : isTriangleInG D := ⟨D_card, D_is_clique⟩
lemma E1_is_triangle : isTriangleInG E1 := ⟨E1_card, E1_is_clique⟩
lemma E2_is_triangle : isTriangleInG E2 := ⟨E2_card, E2_is_clique⟩
lemma E3_is_triangle : isTriangleInG E3 := ⟨E3_card, E3_is_clique⟩
lemma E4_is_triangle : isTriangleInG E4 := ⟨E4_card, E4_is_clique⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 8: Triangle Enumeration
-- ══════════════════════════════════════════════════════════════════════════════

/-- The triangles in G are exactly M ∪ externals -/
lemma triangles_eq : trianglesInG = M ∪ externals := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 9: Cover Construction (8 edges)
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 8-edge cover:
    Pair 1 (A,B): spokes {0,1}, {0,3} + bases {1,2}, {3,4}
    Pair 2 (C,D): spokes {5,6}, {5,8} + bases {6,7}, {8,9}
-/
def cover : Finset (Finset V) :=
  { {0, 1},   -- spoke from v, hits A
    {0, 3},   -- spoke from v, hits B
    {1, 2},   -- base of A, hits E1
    {3, 4},   -- base of B, hits E2
    {5, 6},   -- spoke from w, hits C
    {5, 8},   -- spoke from w, hits D
    {6, 7},   -- base of C, hits E3
    {8, 9} }  -- base of D, hits E4

lemma cover_card : cover.card = 8 := by native_decide

lemma cover_all_edges : ∀ e ∈ cover, e.card = 2 := by
  intro e he
  simp only [cover, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 10: Coverage Verification
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_01_in_A : {(0 : V), 1} ⊆ A := by native_decide
lemma edge_03_in_B : {(0 : V), 3} ⊆ B := by native_decide
lemma edge_56_in_C : {(5 : V), 6} ⊆ C := by native_decide
lemma edge_58_in_D : {(5 : V), 8} ⊆ D := by native_decide

lemma edge_12_in_E1 : {(1 : V), 2} ⊆ E1 := by native_decide
lemma edge_34_in_E2 : {(3 : V), 4} ⊆ E2 := by native_decide
lemma edge_67_in_E3 : {(6 : V), 7} ⊆ E3 := by native_decide
lemma edge_89_in_E4 : {(8 : V), 9} ⊆ E4 := by native_decide

lemma cover_hits_A : ∃ e ∈ cover, e ⊆ A := ⟨{0, 1}, by native_decide, edge_01_in_A⟩
lemma cover_hits_B : ∃ e ∈ cover, e ⊆ B := ⟨{0, 3}, by native_decide, edge_03_in_B⟩
lemma cover_hits_C : ∃ e ∈ cover, e ⊆ C := ⟨{5, 6}, by native_decide, edge_56_in_C⟩
lemma cover_hits_D : ∃ e ∈ cover, e ⊆ D := ⟨{5, 8}, by native_decide, edge_58_in_D⟩

lemma cover_hits_E1 : ∃ e ∈ cover, e ⊆ E1 := ⟨{1, 2}, by native_decide, edge_12_in_E1⟩
lemma cover_hits_E2 : ∃ e ∈ cover, e ⊆ E2 := ⟨{3, 4}, by native_decide, edge_34_in_E2⟩
lemma cover_hits_E3 : ∃ e ∈ cover, e ⊆ E3 := ⟨{6, 7}, by native_decide, edge_67_in_E3⟩
lemma cover_hits_E4 : ∃ e ∈ cover, e ⊆ E4 := ⟨{8, 9}, by native_decide, edge_89_in_E4⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 11: Main Theorems
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for cover_hits_all_triangles:
1. By triangles_eq, all triangles are in M ∪ externals
2. For M-triangles: spokes from v hit A,B; spokes from w hit C,D
3. For externals: base edges hit each external
4. Cover contains both spokes and bases
5. Therefore cover hits all triangles
-/

/-- Cover hits all triangles in G -/
theorem cover_hits_all_triangles : ∀ T ∈ trianglesInG, ∃ e ∈ cover, e ⊆ T := by
  intro T hT
  rw [triangles_eq] at hT
  simp only [M, externals, mem_union, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cover_hits_A
  · exact cover_hits_B
  · exact cover_hits_C
  · exact cover_hits_D
  · exact cover_hits_E1
  · exact cover_hits_E2
  · exact cover_hits_E3
  · exact cover_hits_E4

/-
PROOF SKETCH for two_two_vw_phase2_tau_le_8:
1. Cover has 8 edges
2. Each edge has exactly 2 vertices (valid edge)
3. Cover hits all triangles (by cover_hits_all_triangles)
4. Therefore τ ≤ 8 = 2ν (Tuza's bound)
-/

/-- TWO_TWO_VW Phase 2: τ ≤ 8 = 2ν (Tuza's bound achieved) -/
theorem two_two_vw_phase2_tau_le_8 :
    ∃ E : Finset (Finset V),
      E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  use cover
  refine ⟨?_, cover_all_edges, cover_hits_all_triangles⟩
  simp only [cover_card, le_refl]

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

/-- Key property: No inter-pair bridges exist -/
theorem no_inter_pair_bridges :
    ∀ T ∈ externals,
      -- T shares edge with at most one of {A,B}
      ((T ∩ A).card = 2 → (T ∩ B).card = 0) ∧
      ((T ∩ B).card = 2 → (T ∩ A).card = 0) ∧
      -- T shares edge with at most one of {C,D}
      ((T ∩ C).card = 2 → (T ∩ D).card = 0) ∧
      ((T ∩ D).card = 2 → (T ∩ C).card = 0) ∧
      -- T doesn't bridge across pairs
      ((T ∩ A).card = 2 ∨ (T ∩ B).card = 2 → (T ∩ C).card = 0 ∧ (T ∩ D).card = 0) ∧
      ((T ∩ C).card = 2 ∨ (T ∩ D).card = 2 → (T ∩ A).card = 0 ∧ (T ∩ B).card = 0) := by
  intro T hT
  simp only [externals, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl
  -- E1
  · refine ⟨fun _ => E1_inter_B, fun h => ?_, fun _ => ?_, fun _ => ?_, ?_, ?_⟩
    · simp only [E1_inter_B] at h; omega
    · simp only [E1_inter_D] at *; omega
    · simp only [E1_inter_D] at *; omega
    · intro _; exact ⟨E1_inter_C, E1_inter_D⟩
    · intro h; rcases h with h | h <;> simp_all [E1_inter_C, E1_inter_D]
  -- E2
  · refine ⟨fun h => ?_, fun _ => E2_inter_A, fun _ => ?_, fun _ => ?_, ?_, ?_⟩
    · simp only [E2_inter_A] at h; omega
    · simp only [E2_inter_D] at *; omega
    · simp only [E2_inter_D] at *; omega
    · intro _; exact ⟨E2_inter_C, E2_inter_D⟩
    · intro h; rcases h with h | h <;> simp_all [E2_inter_C, E2_inter_D]
  -- E3
  · refine ⟨fun _ => ?_, fun _ => ?_, fun _ => E3_inter_D, fun h => ?_, ?_, ?_⟩
    · simp only [E3_inter_A, E3_inter_B] at *; omega
    · simp only [E3_inter_A, E3_inter_B] at *; omega
    · simp only [E3_inter_D] at h; omega
    · intro h; rcases h with h | h <;> simp_all [E3_inter_A, E3_inter_B]
    · intro _; exact ⟨E3_inter_A, E3_inter_B⟩
  -- E4
  · refine ⟨fun _ => ?_, fun _ => ?_, fun h => ?_, fun _ => E4_inter_C, ?_, ?_⟩
    · simp only [E4_inter_A, E4_inter_B] at *; omega
    · simp only [E4_inter_A, E4_inter_B] at *; omega
    · simp only [E4_inter_C] at h; omega
    · intro h; rcases h with h | h <;> simp_all [E4_inter_A, E4_inter_B]
    · intro _; exact ⟨E4_inter_A, E4_inter_B⟩

/-- Summary: Two_two_vw Phase 2 achieves τ ≤ 8 = 2ν -/
theorem two_two_vw_summary :
    M.card = 4 ∧
    trianglesInG.card = 8 ∧  -- 4 M-triangles + 4 externals
    cover.card = 8 ∧
    (∀ T ∈ trianglesInG, ∃ e ∈ cover, e ⊆ T) := by
  refine ⟨M_card, ?_, cover_card, cover_hits_all_triangles⟩
  rw [triangles_eq]
  native_decide

end TwoTwoVWPhase2
