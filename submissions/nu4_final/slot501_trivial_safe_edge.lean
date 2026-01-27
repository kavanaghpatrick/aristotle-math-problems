/-
  slot501_trivial_safe_edge.lean

  INSIGHT: The exists_safe_edge theorem is TRIVIALLY TRUE.

  For any edge e of M-element m, and any triangle t ≠ m containing e:
  - t and m SHARE edge e
  - So t is NOT edge-disjoint from m
  - But m ∈ {m0, m1, m2, m3}
  - So t fails the "disjoint from all M-elements" condition

  Therefore: EVERY edge of every M-element has no externals!
  No pigeonhole or shared vertex argument needed.

  TIER: 1 (direct set membership)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

abbrev V9 := Fin 9

def mkE (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

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

def pack4 (m0 m1 m2 m3 : Tri) : Prop :=
  edgeDisj m0 m1 ∧ edgeDisj m0 m2 ∧ edgeDisj m0 m3 ∧
  edgeDisj m1 m2 ∧ edgeDisj m1 m3 ∧ edgeDisj m2 m3

instance (m0 m1 m2 m3 : Tri) : Decidable (pack4 m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- Definition: edge e of m has no external triangles
def hasNoExternal (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, e ∈ t.edges → e ∈ m.edges → t ≠ m →
    ¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3

-- Key lemma: if t and m share an edge, they're not disjoint
lemma sharing_edge_not_disjoint (t m : Tri) (e : V9 × V9)
    (he_t : e ∈ t.edges) (he_m : e ∈ m.edges) :
    ¬edgeDisj t m := by
  unfold edgeDisj
  exact Finset.not_disjoint_iff.mpr ⟨e, he_t, he_m⟩

-- Any edge of any M-element has no externals (TRIVIALLY TRUE)
lemma any_edge_safe (m0 m1 m2 m3 m : Tri) (e : V9 × V9)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3)
    (he : e ∈ m.edges) :
    hasNoExternal m e m0 m1 m2 m3 := by
  intro t ht_e ht_m ht_ne
  -- t contains edge e, and m contains edge e
  -- So t and m share edge e → t is not edge-disjoint from m
  -- Since m is one of m0, m1, m2, m3, we get one of the disjuncts
  rcases hm with rfl | rfl | rfl | rfl
  all_goals first
  | { left; exact sharing_edge_not_disjoint t _ e ht_e ht_m }
  | { right; left; exact sharing_edge_not_disjoint t _ e ht_e ht_m }
  | { right; right; left; exact sharing_edge_not_disjoint t _ e ht_e ht_m }
  | { right; right; right; exact sharing_edge_not_disjoint t _ e ht_e ht_m }

lemma e1_in_edges (m : Tri) : m.e1 ∈ m.edges := by
  unfold Tri.edges; simp

lemma e2_in_edges (m : Tri) : m.e2 ∈ m.edges := by
  unfold Tri.edges; simp

lemma e3_in_edges (m : Tri) : m.e3 ∈ m.edges := by
  unfold Tri.edges; simp

-- Main theorem: exists_safe_edge (TRIVIALLY TRUE - all edges are safe!)
theorem exists_safe_edge (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    hasNoExternal m m.e1 m0 m1 m2 m3 ∨
    hasNoExternal m m.e2 m0 m1 m2 m3 ∨
    hasNoExternal m m.e3 m0 m1 m2 m3 := by
  -- In fact, ALL THREE edges are safe, so we just pick e1
  left
  exact any_edge_safe m0 m1 m2 m3 m m.e1 hm (e1_in_edges m)

-- Stronger result: ALL edges are safe
theorem all_edges_safe (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    hasNoExternal m m.e1 m0 m1 m2 m3 ∧
    hasNoExternal m m.e2 m0 m1 m2 m3 ∧
    hasNoExternal m m.e3 m0 m1 m2 m3 := by
  constructor
  · exact any_edge_safe m0 m1 m2 m3 m m.e1 hm (e1_in_edges m)
  constructor
  · exact any_edge_safe m0 m1 m2 m3 m m.e2 hm (e2_in_edges m)
  · exact any_edge_safe m0 m1 m2 m3 m m.e3 hm (e3_in_edges m)
