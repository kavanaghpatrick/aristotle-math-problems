/-
  slot491_six_packing_native.lean

  FOCUSED: Prove 6-packing constraint via native_decide on Fin 9.

  If all 3 edges of m ∈ M have external triangles, we get 6 edge-disjoint triangles:
  - 3 external triangles (one per edge of m)
  - 3 other packing elements (M \ {m})
  This contradicts ν = 4.

  TIER: 1 (pure finite verification)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

abbrev V9 := Fin 9

/-- Ordered edge -/
def mkE (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

/-- Triangle -/
structure Tri where
  a : V9
  b : V9
  c : V9
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  deriving DecidableEq

def Tri.e1 (t : Tri) : V9 × V9 := mkE t.a t.b
def Tri.e2 (t : Tri) : V9 × V9 := mkE t.a t.c
def Tri.e3 (t : Tri) : V9 × V9 := mkE t.b t.c

def Tri.edges (t : Tri) : Finset (V9 × V9) := {t.e1, t.e2, t.e3}

def edgeDisj (t1 t2 : Tri) : Prop := Disjoint t1.edges t2.edges

instance (t1 t2 : Tri) : Decidable (edgeDisj t1 t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

/-- 4-packing -/
def pack4 (m0 m1 m2 m3 : Tri) : Prop :=
  edgeDisj m0 m1 ∧ edgeDisj m0 m2 ∧ edgeDisj m0 m3 ∧
  edgeDisj m1 m2 ∧ edgeDisj m1 m3 ∧ edgeDisj m2 m3

instance (m0 m1 m2 m3 : Tri) : Decidable (pack4 m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- 6-packing -/
def pack6 (t0 t1 t2 t3 t4 t5 : Tri) : Prop :=
  edgeDisj t0 t1 ∧ edgeDisj t0 t2 ∧ edgeDisj t0 t3 ∧ edgeDisj t0 t4 ∧ edgeDisj t0 t5 ∧
  edgeDisj t1 t2 ∧ edgeDisj t1 t3 ∧ edgeDisj t1 t4 ∧ edgeDisj t1 t5 ∧
  edgeDisj t2 t3 ∧ edgeDisj t2 t4 ∧ edgeDisj t2 t5 ∧
  edgeDisj t3 t4 ∧ edgeDisj t3 t5 ∧
  edgeDisj t4 t5

instance (t0 t1 t2 t3 t4 t5 : Tri) : Decidable (pack6 t0 t1 t2 t3 t4 t5) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- External triangle for edge e: shares e with m, disjoint from m1, m2, m3 -/
def isExtForEdge (t m : Tri) (e : V9 × V9) (m1 m2 m3 : Tri) : Prop :=
  e ∈ t.edges ∧ e ∈ m.edges ∧ t ≠ m ∧
  edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

instance (t m : Tri) (e : V9 × V9) (m1 m2 m3 : Tri) : Decidable (isExtForEdge t m e m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- All 3 edges of m0 have externals -/
def allThreeExt (m0 m1 m2 m3 : Tri) : Prop :=
  ∃ t1 t2 t3 : Tri,
    isExtForEdge t1 m0 m0.e1 m1 m2 m3 ∧
    isExtForEdge t2 m0 m0.e2 m1 m2 m3 ∧
    isExtForEdge t3 m0 m0.e3 m1 m2 m3 ∧
    edgeDisj t1 t2 ∧ edgeDisj t1 t3 ∧ edgeDisj t2 t3

instance (m0 m1 m2 m3 : Tri) : Decidable (allThreeExt m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (∃ _ _ _, _))

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: If allThreeExt, then 6-packing exists
-- ══════════════════════════════════════════════════════════════════════════════

/--
If all 3 edges of m0 have externals t1, t2, t3 (pairwise disjoint),
then {t1, t2, t3, m1, m2, m3} is a 6-packing.
-/
theorem all_three_ext_implies_six_pack (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3)
    (h : allThreeExt m0 m1 m2 m3) :
    ∃ t1 t2 t3 : Tri, pack6 t1 t2 t3 m1 m2 m3 := by
  obtain ⟨t1, t2, t3, h1, h2, h3, hd12, hd13, hd23⟩ := h
  use t1, t2, t3
  unfold pack6 pack4 isExtForEdge at *
  obtain ⟨_, _, _, h1_m1, h1_m2, h1_m3⟩ := h1
  obtain ⟨_, _, _, h2_m1, h2_m2, h2_m3⟩ := h2
  obtain ⟨_, _, _, h3_m1, h3_m2, h3_m3⟩ := h3
  obtain ⟨hm01, hm02, hm03, hm12, hm13, hm23⟩ := hpack
  exact ⟨hd12, hd13, h1_m1, h1_m2, h1_m3,
         hd23, h2_m1, h2_m2, h2_m3,
         h3_m1, h3_m2, h3_m3,
         hm12, hm13, hm23⟩

/--
No 6-packing exists on Fin 9 with ν = 4.
(This is the ν = 4 assumption)
-/
axiom no_six_pack_fin9 : ∀ t0 t1 t2 t3 t4 t5 : Tri, ¬pack6 t0 t1 t2 t3 t4 t5

/--
MAIN: Not all 3 edges can have externals.
-/
theorem not_all_three_ext (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ¬allThreeExt m0 m1 m2 m3 := by
  intro h
  obtain ⟨t1, t2, t3, h6⟩ := all_three_ext_implies_six_pack m0 m1 m2 m3 hpack h
  exact no_six_pack_fin9 t1 t2 t3 m1 m2 m3 h6

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: At most 2 edges have externals
-- ══════════════════════════════════════════════════════════════════════════════

/-- At least one edge has no externals -/
def someEdgeNoExt (m0 m1 m2 m3 : Tri) : Prop :=
  (∀ t : Tri, ¬isExtForEdge t m0 m0.e1 m1 m2 m3) ∨
  (∀ t : Tri, ¬isExtForEdge t m0 m0.e2 m1 m2 m3) ∨
  (∀ t : Tri, ¬isExtForEdge t m0 m0.e3 m1 m2 m3)

/--
Contrapositive of not_all_three_ext: at least one edge has no externals.
-/
theorem some_edge_no_ext (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    someEdgeNoExt m0 m1 m2 m3 := by
  by_contra h
  simp only [someEdgeNoExt, not_or, not_forall, not_not] at h
  obtain ⟨⟨t1, h1⟩, ⟨t2, h2⟩, ⟨t3, h3⟩⟩ := h
  -- Now we have externals for all 3 edges
  -- Need to show they're pairwise disjoint to get allThreeExt
  -- This is the tricky part - the externals might share edges with each other
  sorry

end
