/-
  slot550: CONCRETE PATH_4 τ ≤ 8 PROOF ON Fin 9

  Demonstrates the proof strategy for Tuza's conjecture ν=4, PATH_4 case.
  ALL verification by native_decide — sorry=0, axiom=0.

  Graph: 9 vertices, 14 edges, 7 triangles
  Packing: A={0,1,2}, B={1,3,4}, C={4,5,6}, D={6,7,8}
  PATH_4 structure: A—[1]—B—[4]—C—[6]—D

  Extra edges: 0-3, 2-3 (connecting A's base vertices to B's non-spine vertex)
  This creates:
  - 1 external of A: {0,2,3} (shares base edge {0,2})
  - 2 A-B bridges: {0,1,3} and {1,2,3}
  All three extras share pairwise ≥2 vertices, so ν stays at 4.

  Cover: 8 edges (we construct an explicit cover, not necessarily tight)

  SORRY COUNT: 0
  AXIOM COUNT: 0
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators

-- ═══════════════════════════════════════════════════════════════
-- FINITE TYPE
-- ═══════════════════════════════════════════════════════════════

abbrev V9 := Fin 9

-- ═══════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ═══════════════════════════════════════════════════════════════

/-- Triangle packing: pairwise share at most 1 vertex -/
def isTrianglePacking (S : Finset (Finset V9)) : Prop :=
  ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1

-- ═══════════════════════════════════════════════════════════════
-- GRAPH: ALL TRIANGLES (explicitly enumerated)
-- ═══════════════════════════════════════════════════════════════

/-- The graph has exactly these 7 triangles -/
def allTriangles : Finset (Finset V9) := {
  {0, 1, 2},     -- A (packing element)
  {1, 3, 4},     -- B (packing element)
  {4, 5, 6},     -- C (packing element)
  {6, 7, 8},     -- D (packing element)
  {0, 2, 3},     -- External of A (shares base edge {0,2})
  {0, 1, 3},     -- Bridge A-B (shares {0,1} with A, {1,3} with B)
  {1, 2, 3}      -- Bridge A-B (shares {1,2} with A, {1,3} with B)
}

/-- Edge set of the graph -/
def graphEdges : Finset (Finset V9) := {
  {0, 1}, {0, 2}, {1, 2},           -- Triangle A
  {1, 3}, {1, 4}, {3, 4},           -- Triangle B
  {4, 5}, {4, 6}, {5, 6},           -- Triangle C
  {6, 7}, {6, 8}, {7, 8},           -- Triangle D
  {0, 3}, {2, 3}                    -- Extra edges (create external + bridges)
}

-- ═══════════════════════════════════════════════════════════════
-- VERIFY: allTriangles is complete (no other triangle exists)
-- ═══════════════════════════════════════════════════════════════

/-- Every card-3 subset of V9 whose pairs are all graph edges is in allTriangles -/
lemma allTriangles_complete :
    ∀ T ∈ (Finset.univ : Finset V9).powerset,
      T.card = 3 →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ({x, y} : Finset V9) ∈ graphEdges) →
      T ∈ allTriangles := by
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- PACKING AND PATH_4 STRUCTURE
-- ═══════════════════════════════════════════════════════════════

def A_tri : Finset V9 := {0, 1, 2}
def B_tri : Finset V9 := {1, 3, 4}
def C_tri : Finset V9 := {4, 5, 6}
def D_tri : Finset V9 := {6, 7, 8}

def M : Finset (Finset V9) := {A_tri, B_tri, C_tri, D_tri}

-- PATH_4 structure verified
#check (by native_decide : M.card = 4)
#check (by native_decide : (A_tri ∩ B_tri).card = 1)
#check (by native_decide : (B_tri ∩ C_tri).card = 1)
#check (by native_decide : (C_tri ∩ D_tri).card = 1)
#check (by native_decide : (A_tri ∩ C_tri).card = 0)
#check (by native_decide : (A_tri ∩ D_tri).card = 0)
#check (by native_decide : (B_tri ∩ D_tri).card = 0)

-- Valid packing
lemma M_packing : isTrianglePacking M := by
  unfold isTrianglePacking M A_tri B_tri C_tri D_tri
  native_decide

-- Maximal: every non-packing triangle shares ≥2 vertices with some element
lemma M_maximal :
    ∀ T ∈ allTriangles, T ∉ M →
      ∃ m ∈ M, (T ∩ m).card ≥ 2 := by
  unfold allTriangles M A_tri B_tri C_tri D_tri
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- ν = 4: NO 5-PACKING EXISTS
-- ═══════════════════════════════════════════════════════════════

lemma nu_eq_4 :
    ∀ P ∈ allTriangles.powerset,
      isTrianglePacking P → P.card ≤ 4 := by
  unfold isTrianglePacking allTriangles
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- 8-EDGE TRIANGLE COVER
-- ═══════════════════════════════════════════════════════════════

/--
Cover construction:
  s(0,1) covers A={0,1,2} and bridge {0,1,3}
  s(0,2) covers A={0,1,2} and ext {0,2,3}
  s(1,3) covers B={1,3,4} and bridge {0,1,3} and bridge {1,2,3}
  s(3,4) covers B={1,3,4}
  s(4,5) covers C={4,5,6}
  s(5,6) covers C={4,5,6}
  s(6,7) covers D={6,7,8}
  s(7,8) covers D={6,7,8}
-/
def cover : Finset (Sym2 V9) := {
  s((0 : V9), 1),
  s((0 : V9), 2),
  s((1 : V9), 3),
  s((3 : V9), 4),
  s((4 : V9), 5),
  s((5 : V9), 6),
  s((6 : V9), 7),
  s((7 : V9), 8)
}

-- Cover has exactly 8 edges
lemma cover_card : cover.card = 8 := by native_decide

-- Cover hits every triangle
lemma cover_complete :
    ∀ T ∈ allTriangles, ∃ e ∈ cover, e ∈ T.sym2 := by
  unfold allTriangles cover
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for this PATH_4 graph
-- ═══════════════════════════════════════════════════════════════

/--
For this concrete PATH_4 graph on Fin 9 with ν = 4:
- The packing {A,B,C,D} has PATH_4 structure
- No 5-packing exists among the graph's 7 triangles
- An 8-edge cover exists that hits every triangle
- Therefore τ ≤ 2ν for this instance

Note: This graph has τ = 4 (tight cover exists with 4 edges),
so the 8-edge bound is not tight. The value is in demonstrating
the sorry=0, native_decide proof pattern on a concrete PATH_4 instance.
-/
theorem path4_tau_le_8_concrete :
    isTrianglePacking M ∧
    M.card = 4 ∧
    (∀ P ∈ allTriangles.powerset, isTrianglePacking P → P.card ≤ 4) ∧
    cover.card ≤ 8 ∧
    (∀ T ∈ allTriangles, ∃ e ∈ cover, e ∈ T.sym2) := by
  exact ⟨M_packing, by native_decide, nu_eq_4, by native_decide, cover_complete⟩
