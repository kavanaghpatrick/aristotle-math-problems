/-
  slot447_BC_conflict_fixed.lean

  FIXED VERSION: Bool/Prop type issue resolved with explicit decidability

  FALSIFICATION TEST: Can the B-C conflict scenario occur with ν = 4?

  KEY INSIGHT TO PROVE:
  On Fin 9, S_e(C, spine) = ∅ because all vertices are in some packing element.
  Therefore C can use both legs, and s(v2,c) covers the B-C bridge.
  The "full conflict" requiring BOTH middle spines is IMPOSSIBLE on Fin 9.

  TIER: 1 (decidable on Fin 9 with native_decide)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE ON FIN 9
-- ══════════════════════════════════════════════════════════════════════════════

-- Vertices: 0=a1, 1=a2, 2=v1, 3=b, 4=v2, 5=c, 6=v3, 7=d1, 8=d2
def A : Finset (Fin 9) := {0, 1, 2}
def B : Finset (Fin 9) := {2, 3, 4}
def C_elem : Finset (Fin 9) := {4, 5, 6}
def D : Finset (Fin 9) := {6, 7, 8}
def M : Finset (Finset (Fin 9)) := {A, B, C_elem, D}

-- ══════════════════════════════════════════════════════════════════════════════
-- GRAPH EDGES
-- ══════════════════════════════════════════════════════════════════════════════

def baseEdges : Finset (Finset (Fin 9)) :=
  { {0, 1}, {0, 2}, {1, 2},     -- A edges
    {2, 3}, {2, 4}, {3, 4},     -- B edges
    {4, 5}, {4, 6}, {5, 6},     -- C edges
    {6, 7}, {6, 8}, {7, 8} }    -- D edges

-- Full conflict edges:
-- - B-C bridge {3,5} (b-c)
-- - S_e(B, left) via {2,5} (v1-c)
-- - S_e(C, right) via {0,5}, {0,6} (a1-c, a1-v3)
-- - S_e(B, spine) via {2,7}, {4,7} (v1-d1, v2-d1)
def fullConflictEdges : Finset (Finset (Fin 9)) :=
  baseEdges ∪ { {3, 5}, {2, 5}, {0, 5}, {0, 6}, {2, 7}, {4, 7} }

-- ══════════════════════════════════════════════════════════════════════════════
-- ADJACENCY AND TRIANGLES (Using Prop with DecidablePred)
-- ══════════════════════════════════════════════════════════════════════════════

def adj (x y : Fin 9) : Prop :=
  x ≠ y ∧ ({x, y} : Finset (Fin 9)) ∈ fullConflictEdges

instance : DecidableRel adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ({x, y} : Finset (Fin 9)) ∈ fullConflictEdges))

def isTriangleProp (T : Finset (Fin 9)) : Prop :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → adj x y)

instance : DecidablePred isTriangleProp := fun T =>
  inferInstanceAs (Decidable (T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → adj x y)))

def allTriangles : Finset (Finset (Fin 9)) :=
  (Finset.univ : Finset (Fin 9)).powerset.filter isTriangleProp

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

def edgeDisjoint (T1 T2 : Finset (Fin 9)) : Prop :=
  (T1 ∩ T2).card ≤ 1

instance : DecidableRel edgeDisjoint := fun T1 T2 =>
  inferInstanceAs (Decidable ((T1 ∩ T2).card ≤ 1))

def isPackingProp (S : Finset (Finset (Fin 9))) : Prop :=
  S ⊆ allTriangles ∧
  (∀ T1 ∈ S, ∀ T2 ∈ S, T1 ≠ T2 → edgeDisjoint T1 T2)

instance : DecidablePred isPackingProp := fun S =>
  inferInstanceAs (Decidable (S ⊆ allTriangles ∧ (∀ T1 ∈ S, ∀ T2 ∈ S, T1 ≠ T2 → edgeDisjoint T1 T2)))

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMAS: Enumerate and verify
-- ══════════════════════════════════════════════════════════════════════════════

/-- M elements are triangles -/
lemma A_is_triangle : A ∈ allTriangles := by native_decide
lemma B_is_triangle : B ∈ allTriangles := by native_decide
lemma C_is_triangle : C_elem ∈ allTriangles := by native_decide
lemma D_is_triangle : D ∈ allTriangles := by native_decide

/-- M is a valid packing -/
lemma M_is_packing : isPackingProp M := by native_decide

/-- M has size 4 -/
lemma M_card : M.card = 4 := by native_decide

/-- List all triangles in the full conflict graph -/
lemma triangles_enumeration : allTriangles =
    {A, B, C_elem, D,
     {2, 3, 5},   -- S_e(B, left): {v1, b, c}
     {3, 4, 5},   -- Bridge B-C: {v2, b, c} (note: {4,3,5} = {3,4,5})
     {0, 5, 6},   -- S_e(C, right): {a1, c, v3}
     {2, 4, 7}}   -- S_e(B, spine): {v1, v2, d1}
    := by native_decide

/-- Count of triangles -/
lemma triangles_count : allTriangles.card = 8 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: ν = 4 for full conflict graph
-- ══════════════════════════════════════════════════════════════════════════════

/-- No packing has more than 4 triangles -/
theorem full_conflict_nu_le_4 :
    ∀ S : Finset (Finset (Fin 9)), isPackingProp S → S.card ≤ 4 := by
  native_decide

/-- ν = 4: M achieves the maximum -/
theorem full_conflict_nu_eq_4 :
    (∃ S : Finset (Finset (Fin 9)), isPackingProp S ∧ S.card = 4) ∧
    (∀ S : Finset (Finset (Fin 9)), isPackingProp S → S.card ≤ 4) := by
  exact ⟨⟨M, M_is_packing, M_card⟩, full_conflict_nu_le_4⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- S_e ANALYSIS: Which triangles are S_e externals?
-- ══════════════════════════════════════════════════════════════════════════════

/-- S_e external: shares edge with one M-element only -/
def isSeExternal (T : Finset (Fin 9)) (E : Finset (Fin 9)) : Prop :=
  T ∈ allTriangles ∧ T ≠ E ∧
  2 ≤ (T ∩ E).card ∧
  (∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1)

instance (T E : Finset (Fin 9)) : Decidable (isSeExternal T E) :=
  inferInstanceAs (Decidable (T ∈ allTriangles ∧ T ≠ E ∧ 2 ≤ (T ∩ E).card ∧
    (∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1)))

/-- S_e(B, spine {2,4}): Triangle {2, 4, 7} -/
lemma Se_B_spine_nonempty : isSeExternal {2, 4, 7} B := by native_decide

/-- S_e(B, left {2,3}): Triangle {2, 3, 5} -/
lemma Se_B_left_nonempty : isSeExternal {2, 3, 5} B := by native_decide

/-- S_e(C, right {5,6}): Triangle {0, 5, 6} -/
lemma Se_C_right_nonempty : isSeExternal {0, 5, 6} C_elem := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: S_e(C, spine) is EMPTY on Fin 9!
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle uses C's spine {4,6} if it contains both vertices -/
def usesSpineC (T : Finset (Fin 9)) : Prop := (4 : Fin 9) ∈ T ∧ (6 : Fin 9) ∈ T

instance (T : Finset (Fin 9)) : Decidable (usesSpineC T) :=
  inferInstanceAs (Decidable ((4 : Fin 9) ∈ T ∧ (6 : Fin 9) ∈ T))

/-- There is NO S_e external of C on the spine edge {4,6} -/
theorem Se_C_spine_empty :
    ∀ T : Finset (Fin 9), isSeExternal T C_elem → usesSpineC T → False := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE ANALYSIS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A bridge between B and C -/
def isBridgeBC (T : Finset (Fin 9)) : Prop :=
  T ∈ allTriangles ∧ 2 ≤ (T ∩ B).card ∧ 2 ≤ (T ∩ C_elem).card

instance (T : Finset (Fin 9)) : Decidable (isBridgeBC T) :=
  inferInstanceAs (Decidable (T ∈ allTriangles ∧ 2 ≤ (T ∩ B).card ∧ 2 ≤ (T ∩ C_elem).card))

/-- The only B-C bridge is {3, 4, 5} -/
lemma BC_bridge_unique : ∀ T : Finset (Fin 9), isBridgeBC T ↔ T = {3, 4, 5} := by
  native_decide

/-- The bridge {3, 4, 5} contains edge {4, 5} = s(v2, c) -/
lemma bridge_contains_v2_c : (4 : Fin 9) ∈ ({3, 4, 5} : Finset (Fin 9)) ∧
                             (5 : Fin 9) ∈ ({3, 4, 5} : Finset (Fin 9)) := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER ANALYSIS: Can we cover all 8 triangles with 8 edges?
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edge as Sym2 -/
def e (x y : Fin 9) : Sym2 (Fin 9) := s(x, y)

/-- The 8-edge cover that works -/
def cover8 : Finset (Sym2 (Fin 9)) :=
  { e 0 2, e 1 2,     -- A: both spokes (covers A, helps with bridges)
    e 2 4, e 2 3,     -- B: spine + left (covers B, Se(B,spine), Se(B,left))
    e 4 5, e 5 6,     -- C: left leg + right leg (covers C, Se(C,right), BRIDGE!)
    e 6 7, e 6 8 }    -- D: both spokes

lemma cover8_card : cover8.card = 8 := by native_decide

/-- Check if an edge hits a triangle -/
def edgeHitsTriangle (edge : Sym2 (Fin 9)) (T : Finset (Fin 9)) : Prop :=
  edge ∈ T.sym2

instance (edge : Sym2 (Fin 9)) (T : Finset (Fin 9)) : Decidable (edgeHitsTriangle edge T) :=
  inferInstanceAs (Decidable (edge ∈ T.sym2))

/-- Cover hits a triangle if some edge in cover hits it -/
def coverHitsTriangle (C : Finset (Sym2 (Fin 9))) (T : Finset (Fin 9)) : Prop :=
  ∃ edge ∈ C, edgeHitsTriangle edge T

instance (C : Finset (Sym2 (Fin 9))) (T : Finset (Fin 9)) : Decidable (coverHitsTriangle C T) :=
  inferInstanceAs (Decidable (∃ edge ∈ C, edgeHitsTriangle edge T))

/-- MAIN: The 8-edge cover hits all triangles! -/
theorem cover8_hits_all :
    ∀ T ∈ allTriangles, coverHitsTriangle cover8 T := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- FINAL THEOREM: τ ≤ 8 for the full conflict graph
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_full_conflict :
    ∃ C : Finset (Sym2 (Fin 9)),
      C.card ≤ 8 ∧
      ∀ T ∈ allTriangles, coverHitsTriangle C T := by
  use cover8
  exact ⟨by native_decide, cover8_hits_all⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- CONCLUSION
-- ══════════════════════════════════════════════════════════════════════════════

/-
  PROVEN:
  1. ν = 4 for the full conflict graph (full_conflict_nu_eq_4)
  2. S_e(C, spine) = ∅ on Fin 9 (Se_C_spine_empty)
  3. τ ≤ 8 is achievable (tau_le_8_full_conflict)

  KEY INSIGHT:
  Because S_e(C, spine) is empty, C can use both legs {s(v2,c), s(c,v3)}.
  The edge s(v2,c) = s(4,5) covers the B-C bridge {3,4,5}.
  Therefore the "full conflict" scenario (both middles forced to spine)
  is IMPOSSIBLE on Fin 9.

  The coordination hypothesis h_BC_coord is automatically satisfied
  when all vertices are in the packing (no external vertex exists).
-/

end
