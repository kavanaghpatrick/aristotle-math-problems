/-
  slot493_external_structure.lean

  KEY INSIGHT: External triangles for different edges of m may share vertices.
  If T_ab (external for edge ab) and T_ac (external for edge ac) both exist,
  they both contain vertex a. If they share a third vertex x, they share edge (a,x).

  CASES:
  1. All 3 externals pairwise disjoint → 6-packing → contradiction (ν=4)
  2. Two externals share an edge → they share a common "apex" vertex

  In case 2, the shared apex creates structure we can exploit:
  - If T_ab = {a,b,x} and T_ac = {a,c,x}, edge (a,x) covers both
  - This "apex edge" might be in another packing element!

  TIER: 2 (structural analysis)
-/

import Mathlib

set_option maxHeartbeats 400000

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

def Tri.vertices (t : Tri) : Finset V9 := {t.a, t.b, t.c}
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

/-- External triangle: shares edge e with m, disjoint from m1,m2,m3 -/
def isExt (t m : Tri) (e : V9 × V9) (m1 m2 m3 : Tri) : Prop :=
  e ∈ t.edges ∧ e ∈ m.edges ∧ t ≠ m ∧
  edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: External structure when two externals share a vertex
-- ══════════════════════════════════════════════════════════════════════════════

/--
If T_ab is external for edge (a,b) of m = {a,b,c}, then T_ab = {a,b,x} for some x ≠ a,b,c.
The "apex" of T_ab relative to (a,b) is x.
-/
def apex (t m : Tri) (e : V9 × V9) (h_ext : e ∈ t.edges ∧ e ∈ m.edges ∧ t ≠ m) : V9 :=
  -- The vertex of t not in e
  if t.a ∉ ({e.1, e.2} : Finset V9) then t.a
  else if t.b ∉ ({e.1, e.2} : Finset V9) then t.b
  else t.c

/--
KEY LEMMA: If T1 is external for e1 and T2 is external for e2 (different edges of m),
and T1 and T2 share an edge, then they share the same apex vertex.

PROOF SKETCH:
- m = {a,b,c}, e1 = (a,b), e2 = (a,c)
- T1 = {a,b,x}, T2 = {a,c,y}
- T1 edges: (a,b), (a,x), (b,x)
- T2 edges: (a,c), (a,y), (c,y)
- For T1 and T2 to share an edge:
  - (a,x) = (a,y) implies x = y (same apex)
  - Other cases lead to T1 = m or T2 = m (contradicting external)
-/
lemma shared_edge_implies_same_apex (m t1 t2 : Tri) (e1 e2 : V9 × V9)
    (h1 : isExt t1 m e1 m m m) (h2 : isExt t2 m e2 m m m)
    (he_diff : e1 ≠ e2) (h_share : ¬edgeDisj t1 t2) :
    ∃ x : V9, x ∈ t1.vertices ∧ x ∈ t2.vertices ∧ x ∉ m.vertices := by
  -- If t1 and t2 share an edge but have different m-edges, they must share a non-m vertex
  unfold isExt at h1 h2
  obtain ⟨he1_t1, he1_m, hne1, _, _, _⟩ := h1
  obtain ⟨he2_t2, he2_m, hne2, _, _, _⟩ := h2
  unfold edgeDisj at h_share
  simp only [Set.not_disjoint_iff, Finset.coe_inter] at h_share
  -- There exists a shared edge
  sorry

/--
COROLLARY: If all 3 edges have externals that share edges pairwise,
then all 3 externals share a common apex vertex x ∉ m.
-/
lemma all_share_implies_common_apex (m t1 t2 t3 : Tri)
    (h1 : isExt t1 m m.e1 m m m) (h2 : isExt t2 m m.e2 m m m) (h3 : isExt t3 m m.e3 m m m)
    (h12 : ¬edgeDisj t1 t2) (h13 : ¬edgeDisj t1 t3) (h23 : ¬edgeDisj t2 t3) :
    ∃ x : V9, x ∈ t1.vertices ∧ x ∈ t2.vertices ∧ x ∈ t3.vertices ∧ x ∉ m.vertices := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY INSIGHT: Common apex reduces cover to 3 edges from m
-- ══════════════════════════════════════════════════════════════════════════════

/--
If all externals share a common apex x, then the 3 "spoke" edges from m to x
are NOT edges of m. But the 3 m-edges cover all externals individually.

Actually, we can do better: edge (a,x) covers both T1 and T2 if they share apex x.
But (a,x) might be in another packing element!
-/

/--
MAIN: Cover construction.

For each m ∈ M, we need to cover all triangles sharing an edge with m.
These are:
1. m itself (covered by any edge of m)
2. Other M-elements sharing edge with m (handled by that element)
3. External triangles (disjoint from other M-elements)
4. Bridge triangles (share edge with m AND another M-element)

Bridges are covered by the shared edge with the other M-element.
So we only need to cover externals.

By 6-packing constraint:
- Either some edge of m has no externals → only 2 edges needed
- Or all 3 edges have externals that share edges → common apex structure

In the common apex case, we can still cover with 2 M-edges plus the apex edges.
But apex edges might be in other M-elements already!
-/

/-- Triangles sharing edge e with m, disjoint from m1,m2,m3 -/
def externalsForEdge (m : Tri) (e : V9 × V9) (m1 m2 m3 : Tri) : Finset Tri :=
  -- Can't enumerate over Tri directly on Fin 9 (too many)
  -- Use finite verification on specific configurations
  ∅ -- placeholder

/--
STRATEGY: For the τ ≤ 8 bound, we show:
1. If some edge has no externals → 2 edges suffice for m → 4 × 2 = 8 total
2. If all edges have externals but share apex → special structure allows 2 edges
3. Bridges don't count against m's edge budget (covered elsewhere)
-/
theorem tau_le_8_strategy (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ E : Finset (V9 × V9), E.card ≤ 8 ∧
      E ⊆ m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges ∧
      ∀ t : Tri, (¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3) →
        ∃ e ∈ E, e ∈ t.edges := by
  -- For now, use 3 edges per element (τ ≤ 12) and refine
  use m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges
  refine ⟨?_, ?_, ?_⟩
  · -- Card bound (actually ≤ 12, need refinement)
    sorry
  · -- Subset (trivial)
    intro e he; exact he
  · -- Coverage
    intro t ht
    rcases ht with h0 | h1 | h2 | h3
    · -- t shares edge with m0
      unfold edgeDisj at h0
      simp only [Set.not_disjoint_iff] at h0
      obtain ⟨e, he_t, he_m0⟩ := h0
      exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_left _ he_m0)), he_t⟩
    · -- t shares edge with m1
      unfold edgeDisj at h1
      simp only [Set.not_disjoint_iff] at h1
      obtain ⟨e, he_t, he_m1⟩ := h1
      exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_right _ he_m1)), he_t⟩
    · -- t shares edge with m2
      unfold edgeDisj at h2
      simp only [Set.not_disjoint_iff] at h2
      obtain ⟨e, he_t, he_m2⟩ := h2
      exact ⟨e, mem_union_left _ (mem_union_right _ he_m2), he_t⟩
    · -- t shares edge with m3
      unfold edgeDisj at h3
      simp only [Set.not_disjoint_iff] at h3
      obtain ⟨e, he_t, he_m3⟩ := h3
      exact ⟨e, mem_union_right _ he_m3, he_t⟩

end
