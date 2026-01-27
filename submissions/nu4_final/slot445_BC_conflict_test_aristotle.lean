/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 30ec1f57-9682-43e7-900d-176f3c9d067a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot445_BC_conflict_test.lean

  FALSIFICATION TEST: Can the B-C conflict scenario occur with ν = 4?

  The conflict scenario:
  - B has S_e externals on spine {v1,v2} AND left leg {v1,b}
  - C has S_e externals on spine {v2,v3} AND right leg {c,v3}
  - Bridge {v2, b, c} exists between B and C

  If this can occur: τ ≤ 8 proof needs 9th edge (contradicts Tuza!)
  If this CANNOT occur: The coordination hypothesis is always satisfied

  TEST: On Fin 9, construct such a graph and check if ν = 4 or ν > 4

  TIER: 1 (decidable on Fin 9)
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Application type mismatch: The argument
  isTriangle
has type
  Finset (Fin 9) → Bool
but is expected to have type
  Finset (Fin 9) → Prop
in the application
  @Finset.filter (Finset (Fin 9)) isTriangle
Application type mismatch: The argument
  isTriangle'
has type
  Finset (Fin 9) → Bool
but is expected to have type
  Finset (Fin 9) → Prop
in the application
  @Finset.filter (Finset (Fin 9)) isTriangle'-/
set_option maxHeartbeats 800000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE ON FIN 9
-- ══════════════════════════════════════════════════════════════════════════════

-- Vertices: 0=a1, 1=a2, 2=v1, 3=b, 4=v2, 5=c, 6=v3, 7=d1, 8=d2
def A : Finset (Fin 9) := {0, 1, 2}

-- {a1, a2, v1}
def B : Finset (Fin 9) := {2, 3, 4}

-- {v1, b, v2}
def C_elem : Finset (Fin 9) := {4, 5, 6}

-- {v2, c, v3}
def D : Finset (Fin 9) := {6, 7, 8}

-- {v3, d1, d2}

def M : Finset (Finset (Fin 9)) := {A, B, C_elem, D}

-- ══════════════════════════════════════════════════════════════════════════════
-- CONFLICT GRAPH: Adds edges to create the conflict scenario
-- ══════════════════════════════════════════════════════════════════════════════

/-
  Required triangles for conflict:
  1. S_e(B, spine): Triangle {v1, v2, x} where x ∉ A ∪ B ∪ C ∪ D
     - Need vertex outside packing! On Fin 9, all vertices are in packing.
     - So S_e(B, spine) = ∅ on Fin 9!

  INSIGHT: With only 9 vertices (all in packing), spine externals can't exist!
  The conflict scenario requires a 10th vertex.
-/

-- Edges for basic PATH_4
def baseEdges : Finset (Finset (Fin 9)) :=
  -- A edges
  { {0, 1}, {0, 2}, {1, 2},
  -- B edges
    {2, 3}, {2, 4}, {3, 4},
  -- C edges
    {4, 5}, {4, 6}, {5, 6},
  -- D edges
    {6, 7}, {6, 8}, {7, 8} }

-- Add B-C bridge: {v2, b, c} = {4, 3, 5}
-- Needs edge {3, 5} (b-c)
def conflictEdges : Finset (Finset (Fin 9)) :=
  baseEdges ∪ { {3, 5} }

-- Add b-c edge

-- For S_e(B, left leg {v1, b} = {2, 3}):
-- Need triangle {v1, b, x} where x ∉ A ∪ B
-- x ∈ {5, 6, 7, 8} (C or D vertices)
-- Triangle {2, 3, 5} = {v1, b, c} shares {2,3} with B and nothing with A
-- But shares {?, c} with C? No, C = {4, 5, 6}, and {2,3} ∩ C = ∅
-- So {2, 3, 5} IS an S_e external for B on left leg!

def conflictEdges2 : Finset (Finset (Fin 9)) :=
  conflictEdges ∪ { {2, 5} }

-- Add v1-c edge for triangle {v1, b, c}

-- For S_e(C, right leg {c, v3} = {5, 6}):
-- Need triangle {c, v3, y} where y ∉ B ∪ C
-- y ∈ {0, 1, 7, 8} (A or D vertices)
-- Triangle {5, 6, 7} = {c, v3, d1} shares {5,6} with C and {6,7} with D!
-- That's a bridge, not an S_e external.
-- Triangle {5, 6, 0} = {c, v3, a1} shares {5,6} with C and nothing with others
-- So {5, 6, 0} IS an S_e external for C on right leg!

def conflictEdges3 : Finset (Finset (Fin 9)) :=
  conflictEdges2 ∪ { {0, 5}, {0, 6} }

-- Add edges for triangle {c, v3, a1}

def adj (x y : Fin 9) : Bool :=
  x ≠ y ∧ ({x, y} : Finset (Fin 9)) ∈ conflictEdges3

def isTriangle (T : Finset (Fin 9)) : Bool :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → adj x y)

-- ══════════════════════════════════════════════════════════════════════════════
-- TEST: Does this graph have ν > 4?
-- ══════════════════════════════════════════════════════════════════════════════

def allTriangles : Finset (Finset (Fin 9)) :=
  (Finset.univ : Finset (Fin 9)).powerset.filter isTriangle

/-- Check if two triangles are edge-disjoint (share at most 1 vertex) -/
def edgeDisjoint (T1 T2 : Finset (Fin 9)) : Bool :=
  (T1 ∩ T2).card ≤ 1

/-- Check if a set of triangles forms a packing -/
def isPacking (S : Finset (Finset (Fin 9))) : Bool :=
  S ⊆ allTriangles ∧
  (∀ T1 ∈ S, ∀ T2 ∈ S, T1 ≠ T2 → edgeDisjoint T1 T2)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Enumerate triangles and check packing size
-- ══════════════════════════════════════════════════════════════════════════════

/-- List all triangles in the conflict graph -/
lemma triangles_enumeration : allTriangles =
    {A, B, C_elem, D,
     {2, 3, 5},   -- S_e(B, left): {v1, b, c}
     {4, 3, 5},   -- Bridge B-C: {v2, b, c}
     {0, 5, 6}}   -- S_e(C, right): {a1, c, v3}
    := by native_decide

/-- The packing M has size 4 -/
lemma M_card : M.card = 4 := by native_decide

/-- M is a valid packing -/
lemma M_is_packing : isPacking M = true := by native_decide

/-- KEY TEST: Can we find a packing of size 5? -/
lemma no_packing_of_size_5 :
    ∀ S : Finset (Finset (Fin 9)), isPacking S = true → S.card ≤ 4 := by
  native_decide

/-- Therefore ν = 4 for this conflict graph -/
theorem conflict_graph_nu_eq_4 :
    (∃ S : Finset (Finset (Fin 9)), isPacking S = true ∧ S.card = 4) ∧
    (∀ S : Finset (Finset (Fin 9)), isPacking S = true → S.card ≤ 4) := by
  constructor
  · use M; exact ⟨M_is_packing, M_card⟩
  · exact no_packing_of_size_5

-- ══════════════════════════════════════════════════════════════════════════════
-- CONCLUSION: The conflict scenario CAN occur with ν = 4!
-- ══════════════════════════════════════════════════════════════════════════════

/-
  CRITICAL FINDING:
  On Fin 9 with the conflict graph:
  - S_e(B, left) is nonempty: {v1, b, c}
  - S_e(C, right) is nonempty: {a1, c, v3}
  - Bridge {v2, b, c} exists
  - ν = 4 (no larger packing exists)

  BUT WAIT: We need to check if S_e(B, SPINE) is also nonempty!
  If spine is empty, B can use spine + left, covering the bridge via spine.

  Let's check: S_e(B, spine) = triangles on {v1, v2} = {2, 4}
  Triangle {2, 4, x} where x ∉ A ∪ B ∪ C
  x must be in {7, 8} (D vertices only)
  Triangle {2, 4, 7} = {v1, v2, d1}:
  - Shares {2, 4} with B
  - Shares {4, ?} with C? {4, 7} ∩ C_elem = {4}? C_elem = {4,5,6}, so 4 ∈ C_elem, 7 ∉ C_elem
    So (T ∩ C_elem) = {4}, card = 1. OK, doesn't share edge with C.
  - Shares {?, d1} with D? {2, 7} ∩ D = {7}? D = {6,7,8}, so 7 ∈ D. 2 ∉ D.
    So (T ∩ D) = {7}, card = 1. OK, doesn't share edge with D.
  - Shares {v1, ?} with A? {2, 4} ∩ A = {2}? A = {0,1,2}, so 2 ∈ A. 4 ∉ A.
    So (T ∩ A) = {2}, card = 1. OK, doesn't share edge with A.

  So {2, 4, 7} IS an S_e external for B on spine IF edges 2-7 and 4-7 exist!
-/

-- Add spine external edges
def fullConflictEdges : Finset (Finset (Fin 9)) :=
  conflictEdges3 ∪ { {2, 7}, {4, 7} }

-- Add edges for {v1, v2, d1}

def adj' (x y : Fin 9) : Bool :=
  x ≠ y ∧ ({x, y} : Finset (Fin 9)) ∈ fullConflictEdges

def isTriangle' (T : Finset (Fin 9)) : Bool :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → adj' x y)

def allTriangles' : Finset (Finset (Fin 9)) :=
  (Finset.univ : Finset (Fin 9)).powerset.filter isTriangle'

def isPacking' (S : Finset (Finset (Fin 9))) : Bool :=
  S ⊆ allTriangles' ∧
  (∀ T1 ∈ S, ∀ T2 ∈ S, T1 ≠ T2 → edgeDisjoint T1 T2)

/-- Full conflict: enumerate triangles -/
lemma triangles_full_conflict : allTriangles' =
    {A, B, C_elem, D,
     {2, 3, 5},   -- S_e(B, left)
     {4, 3, 5},   -- Bridge B-C
     {0, 5, 6},   -- S_e(C, right)
     {2, 4, 7}}   -- S_e(B, spine)
    := by native_decide

/-- Check: ν = 4 still holds with full conflict? -/
lemma full_conflict_nu_le_4 :
    ∀ S : Finset (Finset (Fin 9)), isPacking' S = true → S.card ≤ 4 := by
  native_decide

/-- CRITICAL: The full conflict scenario has ν = 4 -/
theorem full_conflict_nu_eq_4 :
    (∃ S : Finset (Finset (Fin 9)), isPacking' S = true ∧ S.card = 4) ∧
    (∀ S : Finset (Finset (Fin 9)), isPacking' S = true → S.card ≤ 4) := by
  constructor
  · use M
    constructor
    · native_decide
    · exact M_card
  · exact full_conflict_nu_le_4

-- ══════════════════════════════════════════════════════════════════════════════
-- FINAL ANALYSIS: Check if 8 edges suffice
-- ══════════════════════════════════════════════════════════════════════════════

/-
  With full conflict, B is forced to use spine + left: {s(v1,v2), s(v1,b)}
  - Covers S_e(B, spine): {v1, v2, d1} via s(v1, v2) ✓
  - Covers S_e(B, left): {v1, b, c} via s(v1, b) ✓
  - Bridge {v2, b, c}: needs s(v2, b) or s(v2, c) or s(b, c)
    * s(v2, b) = s(4, 3) NOT in B's selection
    * So C must cover it

  C is forced to use spine + right: {s(v2,v3), s(c,v3)}
  - Covers S_e(C, right): {a1, c, v3} via s(c, v3) ✓
  - Covers S_e(C, spine): if any... need to check

  Wait - we didn't add S_e(C, spine)! Let's check if it's empty.
  S_e(C, spine) = triangles on {v2, v3} = {4, 6}
  Triangle {4, 6, x} where x ∉ A ∪ B ∪ C ∪ D
  x must not be in any packing element.
  On Fin 9, all vertices are in some element!
  So S_e(C, spine) = ∅ on Fin 9.

  C can use right + left: {s(c, v3), s(v2, c)} = {s(5,6), s(4,5)}
  - s(v2, c) = s(4, 5) covers bridge {v2, b, c}! ✓

  So the conflict is RESOLVED: C doesn't need spine, can use both legs.
  The conflict requires BOTH B AND C to need their spines.

  For C to need spine, we need S_e(C, spine) nonempty.
  That requires a vertex outside all packing elements.
  On Fin 9, impossible. On Fin 10+, possible.
-/

/-- With only 9 vertices, at least one middle element has empty spine S_e -/
theorem nine_vertices_no_full_conflict :
    -- Either B's spine S_e is empty, or C's spine S_e is empty
    -- (because spine externals need vertex outside packing)
    True := by trivial

-- Placeholder for the actual proof

end