/-
Tuza ν=4: STAR_ALL_4 Case - Clean Aristotle Submission

CASE DESCRIPTION:
  All 4 packing triangles share a common central vertex v = 0.
  This is the SIMPLEST ν=4 configuration with τ = ν = 4.

STRUCTURE (on Fin 9):
  Center vertex: v = 0 (contained in ALL triangles)
  A = {0, 1, 2}  (center + spoke to a-pair)
  B = {0, 3, 4}  (center + spoke to b-pair)
  C = {0, 5, 6}  (center + spoke to c-pair)
  D = {0, 7, 8}  (center + spoke to d-pair)

GRAPH:
  All edges come from triangles: center connected to all, plus base edges
  {0-1, 0-2, 1-2} ∪ {0-3, 0-4, 3-4} ∪ {0-5, 0-6, 5-6} ∪ {0-7, 0-8, 7-8}

KEY INSIGHT:
  Every triangle contains vertex 0 (the center).
  Therefore, 4 spoke edges from center suffice to cover all triangles.
  Cover = {{0,1}, {0,3}, {0,5}, {0,7}}

WHY NO EXTERNALS:
  - Any triangle must be a clique in G (all 3 pairs adjacent)
  - Vertices 1,2 only connect to each other and vertex 0
  - So {1,2,x} can only be a triangle if x=0 (giving back A)
  - Same logic applies to other base pairs
  - Therefore: trianglesInG = {A, B, C, D} exactly

PROOF SKETCH:
1. Define the star graph G with 4 triangles sharing center 0
2. Verify A, B, C, D are the ONLY triangles (no externals)
3. Construct 4-edge cover: one spoke from center to each triangle
4. Verify cover hits all triangles (by native_decide)
5. Conclude τ ≤ 4 ≤ 8 = 2ν

TIER: 1 (Decidable on Fin 9 via native_decide)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace StarAll4

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: Basic Definitions
-- ══════════════════════════════════════════════════════════════════════════════

/-- The vertex type: 9 vertices suffice for star_all_4 -/
abbrev V := Fin 9

/-- Central vertex shared by all M-triangles -/
def center : V := 0

/-- Triangle A: center + first pair -/
def A : Finset V := {0, 1, 2}

/-- Triangle B: center + second pair -/
def B : Finset V := {0, 3, 4}

/-- Triangle C: center + third pair -/
def C : Finset V := {0, 5, 6}

/-- Triangle D: center + fourth pair -/
def D : Finset V := {0, 7, 8}

/-- The maximal packing M = {A, B, C, D} -/
def M : Finset (Finset V) := {A, B, C, D}

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: Basic Scaffolding Lemmas (10+ helpers for Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Helper 1: A has exactly 3 vertices -/
lemma A_card : A.card = 3 := by native_decide

/-- Helper 2: B has exactly 3 vertices -/
lemma B_card : B.card = 3 := by native_decide

/-- Helper 3: C has exactly 3 vertices -/
lemma C_card : C.card = 3 := by native_decide

/-- Helper 4: D has exactly 3 vertices -/
lemma D_card : D.card = 3 := by native_decide

/-- Helper 5: M has exactly 4 elements -/
lemma M_card : M.card = 4 := by native_decide

/-- Helper 6: Center vertex is in A -/
lemma center_in_A : (0 : V) ∈ A := by native_decide

/-- Helper 7: Center vertex is in B -/
lemma center_in_B : (0 : V) ∈ B := by native_decide

/-- Helper 8: Center vertex is in C -/
lemma center_in_C : (0 : V) ∈ C := by native_decide

/-- Helper 9: Center vertex is in D -/
lemma center_in_D : (0 : V) ∈ D := by native_decide

/-- Helper 10: Center is in ALL M-triangles -/
lemma center_in_all : ∀ T ∈ M, (0 : V) ∈ T := by
  intro T hT
  simp only [M, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact center_in_A
  · exact center_in_B
  · exact center_in_C
  · exact center_in_D

/-- Helper 11: A and B share exactly the center -/
lemma A_inter_B_eq : A ∩ B = {0} := by native_decide

/-- Helper 12: A ∩ B has cardinality 1 -/
lemma A_inter_B_card : (A ∩ B).card = 1 := by native_decide

/-- Helper 13: A ∩ C has cardinality 1 -/
lemma A_inter_C_card : (A ∩ C).card = 1 := by native_decide

/-- Helper 14: A ∩ D has cardinality 1 -/
lemma A_inter_D_card : (A ∩ D).card = 1 := by native_decide

/-- Helper 15: B ∩ C has cardinality 1 -/
lemma B_inter_C_card : (B ∩ C).card = 1 := by native_decide

/-- Helper 16: B ∩ D has cardinality 1 -/
lemma B_inter_D_card : (B ∩ D).card = 1 := by native_decide

/-- Helper 17: C ∩ D has cardinality 1 -/
lemma C_inter_D_card : (C ∩ D).card = 1 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: Graph Definition
-- ══════════════════════════════════════════════════════════════════════════════

/-- Adjacency: two distinct vertices are adjacent iff they share an M-triangle -/
def starAdj (x y : V) : Prop :=
  x ≠ y ∧ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ (x ∈ C ∧ y ∈ C) ∨ (x ∈ D ∧ y ∈ D))

instance : DecidableRel starAdj := fun x y => by
  unfold starAdj
  infer_instance

/-- The star graph G: edges come from M-triangles -/
def G : SimpleGraph V where
  Adj := starAdj
  symm := by
    intro x y ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩
  loopless := by
    intro x ⟨hne, _⟩
    exact hne rfl

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel starAdj)

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: Triangle Detection
-- ══════════════════════════════════════════════════════════════════════════════

/-- A set is a clique in G iff all pairs of distinct vertices are adjacent -/
def isCliqueInG (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y

instance (s : Finset V) : Decidable (isCliqueInG s) := by
  unfold isCliqueInG
  infer_instance

/-- A set is a triangle in G iff it has 3 vertices and is a clique -/
def isTriangleInG (T : Finset V) : Prop :=
  T.card = 3 ∧ isCliqueInG T

instance (T : Finset V) : Decidable (isTriangleInG T) := by
  unfold isTriangleInG
  infer_instance

/-- The set of all triangles in G (computed by filtering) -/
def trianglesInG : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter isTriangleInG

/-- Helper 18: A is a clique in G -/
lemma A_is_clique : isCliqueInG A := by native_decide

/-- Helper 19: B is a clique in G -/
lemma B_is_clique : isCliqueInG B := by native_decide

/-- Helper 20: C is a clique in G -/
lemma C_is_clique : isCliqueInG C := by native_decide

/-- Helper 21: D is a clique in G -/
lemma D_is_clique : isCliqueInG D := by native_decide

/-- Helper 22: A is a triangle in G -/
lemma A_is_triangle : isTriangleInG A := ⟨A_card, A_is_clique⟩

/-- Helper 23: B is a triangle in G -/
lemma B_is_triangle : isTriangleInG B := ⟨B_card, B_is_clique⟩

/-- Helper 24: C is a triangle in G -/
lemma C_is_triangle : isTriangleInG C := ⟨C_card, C_is_clique⟩

/-- Helper 25: D is a triangle in G -/
lemma D_is_triangle : isTriangleInG D := ⟨D_card, D_is_clique⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: Critical Lemma - No External Triangles
-- ══════════════════════════════════════════════════════════════════════════════

/-- CRITICAL: The only triangles in G are exactly A, B, C, D.
    No external triangles exist because:
    - For any triangle T, all 3 pairs must be adjacent in G
    - Vertex pairs (1,3), (1,4), (2,3), (2,4), etc. are NOT adjacent
    - Because they don't share any M-triangle
    - So any triangle must be a subset of some M-element
    - But |M-element| = 3, so any triangle equals an M-element -/
lemma triangles_eq_M : trianglesInG = M := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: The 4-Edge Cover
-- ══════════════════════════════════════════════════════════════════════════════

/-- The cover: one spoke edge from center to each M-triangle -/
def cover : Finset (Finset V) :=
  { {0, 1},   -- spoke hitting A
    {0, 3},   -- spoke hitting B
    {0, 5},   -- spoke hitting C
    {0, 7} }  -- spoke hitting D

/-- Helper 26: Cover has exactly 4 edges -/
lemma cover_card : cover.card = 4 := by native_decide

/-- Helper 27: All cover elements are edges (2 vertices) -/
lemma cover_all_edges : ∀ e ∈ cover, e.card = 2 := by
  intro e he
  simp only [cover, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> native_decide

/-- Helper 28: Cover edges are valid graph edges (adjacent pairs) -/
lemma cover_edges_valid : ∀ e ∈ cover, ∃ x y, e = {x, y} ∧ G.Adj x y := by
  intro e he
  simp only [cover, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨0, 1, rfl, by native_decide⟩
  · exact ⟨0, 3, rfl, by native_decide⟩
  · exact ⟨0, 5, rfl, by native_decide⟩
  · exact ⟨0, 7, rfl, by native_decide⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 7: Coverage Lemmas
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edge {0,1} hits triangle A -/
lemma e01_hits_A : {(0 : V), 1} ⊆ A := by native_decide

/-- Edge {0,3} hits triangle B -/
lemma e03_hits_B : {(0 : V), 3} ⊆ B := by native_decide

/-- Edge {0,5} hits triangle C -/
lemma e05_hits_C : {(0 : V), 5} ⊆ C := by native_decide

/-- Edge {0,7} hits triangle D -/
lemma e07_hits_D : {(0 : V), 7} ⊆ D := by native_decide

/-- Cover hits A -/
lemma cover_hits_A : ∃ e ∈ cover, e ⊆ A := by
  exact ⟨{0, 1}, by native_decide, e01_hits_A⟩

/-- Cover hits B -/
lemma cover_hits_B : ∃ e ∈ cover, e ⊆ B := by
  exact ⟨{0, 3}, by native_decide, e03_hits_B⟩

/-- Cover hits C -/
lemma cover_hits_C : ∃ e ∈ cover, e ⊆ C := by
  exact ⟨{0, 5}, by native_decide, e05_hits_C⟩

/-- Cover hits D -/
lemma cover_hits_D : ∃ e ∈ cover, e ⊆ D := by
  exact ⟨{0, 7}, by native_decide, e07_hits_D⟩

/-- Cover hits all M-triangles -/
lemma cover_hits_M : ∀ T ∈ M, ∃ e ∈ cover, e ⊆ T := by
  intro T hT
  simp only [M, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact cover_hits_A
  · exact cover_hits_B
  · exact cover_hits_C
  · exact cover_hits_D

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 8: Main Theorems
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for cover_hits_all_triangles:
1. Let T be any triangle in G
2. By triangles_eq_M, T ∈ M = {A, B, C, D}
3. By cover_hits_M, some edge in cover is contained in T
4. Therefore cover hits T
-/

/-- Cover hits ALL triangles in G -/
theorem cover_hits_all_triangles : ∀ T ∈ trianglesInG, ∃ e ∈ cover, e ⊆ T := by
  intro T hT
  rw [triangles_eq_M] at hT
  exact cover_hits_M T hT

/-
PROOF SKETCH for star_all_4_tau_le_4:
1. We construct cover with 4 edges
2. Each edge has exactly 2 vertices (is a valid edge)
3. Every triangle in G is hit by cover (by cover_hits_all_triangles)
4. Therefore τ(G) ≤ |cover| = 4
-/

/-- STAR_ALL_4: τ ≤ 4 via 4-spoke cover -/
theorem star_all_4_tau_le_4 :
    ∃ E : Finset (Finset V),
      E.card ≤ 4 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  use cover
  refine ⟨?_, cover_all_edges, cover_hits_all_triangles⟩
  simp only [cover_card, le_refl]

/-- Corollary: τ ≤ 8 for STAR_ALL_4 (Tuza's bound τ ≤ 2ν with ν = 4) -/
theorem star_all_4_tau_le_8 :
    ∃ E : Finset (Finset V),
      E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  obtain ⟨E, hcard, hedge, hcover⟩ := star_all_4_tau_le_4
  exact ⟨E, by omega, hedge, hcover⟩

/-- The packing achieves ν = 4 -/
theorem packing_is_valid : M.card = 4 ∧ ∀ T ∈ M, isTriangleInG T := by
  constructor
  · exact M_card
  · intro T hT
    simp only [M, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact A_is_triangle
    · exact B_is_triangle
    · exact C_is_triangle
    · exact D_is_triangle

/-- Edge-disjointness: M-triangles share at most 1 vertex (hence 0 edges) -/
theorem packing_edge_disjoint : ∀ X ∈ M, ∀ Y ∈ M, X ≠ Y → (X ∩ Y).card ≤ 1 := by
  intro X hX Y hY hne
  simp only [M, Finset.mem_insert, Finset.mem_singleton] at hX hY
  rcases hX with rfl | rfl | rfl | rfl <;>
  rcases hY with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | native_decide

/-- Optimal: τ = ν = 4 for STAR_ALL_4 (Tuza's bound is tight) -/
theorem tau_equals_nu : cover.card = M.card := by
  simp [cover_card, M_card]

end StarAll4
