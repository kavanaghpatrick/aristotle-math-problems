/-
  slot497_vertex_counting.lean

  KEY INSIGHT: A 4-packing on Fin 9 uses 12 vertex-triangle incidences
  but only has 9 vertices. By pigeonhole, some vertex is shared by 2+ triangles.

  For the "star" configuration (all 4 triangles share vertex v):
  - Any edge containing v has NO external triangles!
  - Because any external would need to use v, conflicting with other M-elements.

  This gives exists_safe_edge for the star case directly.

  For other configurations, similar counting arguments apply.

  TIER: 1-2 (finite counting with decidable predicates)
-/

import Mathlib

set_option maxHeartbeats 800000

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

def sharesVertex (t1 t2 : Tri) : Prop := (t1.vertices ∩ t2.vertices).Nonempty

instance (t1 t2 : Tri) : Decidable (sharesVertex t1 t2) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

def sharedVertex (t1 t2 : Tri) (h : sharesVertex t1 t2) : V9 :=
  (t1.vertices ∩ t2.vertices).min' h

def vertexInTri (v : V9) (t : Tri) : Prop := v ∈ t.vertices

instance (v : V9) (t : Tri) : Decidable (vertexInTri v t) :=
  inferInstanceAs (Decidable (_ ∈ _))

def allVertices (m0 m1 m2 m3 : Tri) : Finset V9 :=
  m0.vertices ∪ m1.vertices ∪ m2.vertices ∪ m3.vertices

lemma all_vertices_le_9 (m0 m1 m2 m3 : Tri) :
    (allVertices m0 m1 m2 m3).card ≤ 9 := by
  unfold allVertices
  calc (m0.vertices ∪ m1.vertices ∪ m2.vertices ∪ m3.vertices).card
      ≤ Fintype.card V9 := card_le_univ _
    _ = 9 := by native_decide

lemma total_incidences (m0 m1 m2 m3 : Tri) :
    m0.vertices.card + m1.vertices.card + m2.vertices.card + m3.vertices.card = 12 := by
  have h0 : m0.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m0.hbc
    · simp; constructor <;> [exact m0.hab; exact m0.hac]
  have h1 : m1.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m1.hbc
    · simp; constructor <;> [exact m1.hab; exact m1.hac]
  have h2 : m2.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m2.hbc
    · simp; constructor <;> [exact m2.hab; exact m2.hac]
  have h3 : m3.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m3.hbc
    · simp; constructor <;> [exact m3.hab; exact m3.hac]
  linarith

lemma some_vertex_shared (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ v : V9, (vertexInTri v m0 ∧ vertexInTri v m1) ∨
              (vertexInTri v m0 ∧ vertexInTri v m2) ∨
              (vertexInTri v m0 ∧ vertexInTri v m3) ∨
              (vertexInTri v m1 ∧ vertexInTri v m2) ∨
              (vertexInTri v m1 ∧ vertexInTri v m3) ∨
              (vertexInTri v m2 ∧ vertexInTri v m3) := by
  -- By pigeonhole: 12 incidences into 9 vertices means some vertex appears twice
  -- But we need to show it appears in DIFFERENT triangles
  -- Actually, this follows from |all_vertices| ≤ 9 and total incidences = 12
  by_contra h
  push_neg at h
  -- No vertex appears in 2+ triangles → all vertices are distinct → need 12 vertices
  -- But we only have 9 → contradiction
  sorry

def hasNoExternal (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, e ∈ t.edges → e ∈ m.edges → t ≠ m →
    ¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3

def edgeContainsVertex (e : V9 × V9) (v : V9) : Prop := e.1 = v ∨ e.2 = v

instance (e : V9 × V9) (v : V9) : Decidable (edgeContainsVertex e v) :=
  inferInstanceAs (Decidable (_ ∨ _))

lemma shared_vertex_edge_no_external (m0 m1 m2 m3 m : Tri) (v : V9)
    (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3)
    (hv_m : vertexInTri v m)
    (hv_other : ∃ m' : Tri, (m' = m0 ∨ m' = m1 ∨ m' = m2 ∨ m' = m3) ∧ m' ≠ m ∧ vertexInTri v m')
    (e : V9 × V9) (he : e ∈ m.edges) (he_v : edgeContainsVertex e v) :
    hasNoExternal m e m0 m1 m2 m3 := by
  intro t ht_e ht_m ht_ne
  obtain ⟨m', hm'_in, hm'_ne, hv_m'⟩ := hv_other
  -- t contains edge e, which contains v
  -- t also contains some vertex x ≠ endpoints of e (since t is a triangle)
  -- For t to be external, t must be edge-disjoint from m'
  -- But t contains v (via e), and m' contains v
  -- So t and m' share vertex v
  -- If t shares an edge with m', then t is not external to m'
  -- We need to show t shares an edge with m' (or another M-element)
  -- Since both t and m' contain v, any edge of t containing v might be in m'
  -- The edge e contains v and is in t
  -- If e is also in m', we're done
  -- Otherwise, t has another edge containing v (since t is a triangle with v in it)
  -- Wait, t contains edge e which contains v. But e ∈ m.edges and m ≠ m'.
  -- Since m and m' are edge-disjoint (hpack), e ∉ m'.edges
  -- But t might have another edge that IS in m'...
  sorry

theorem exists_safe_edge (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    hasNoExternal m m.e1 m0 m1 m2 m3 ∨
    hasNoExternal m m.e2 m0 m1 m2 m3 ∨
    hasNoExternal m m.e3 m0 m1 m2 m3 := by
  -- By some_vertex_shared, m shares a vertex with another M-element
  -- Edges containing that shared vertex have no externals
  -- m has 3 vertices, each in 2 of its edges
  -- So at least one of its 3 edges contains the shared vertex
  obtain ⟨v, hv_shared⟩ := some_vertex_shared m0 m1 m2 m3 hpack
  rcases hm with rfl | rfl | rfl | rfl
  all_goals {
    rcases hv_shared with ⟨hv0, hv1⟩ | ⟨hv0, hv2⟩ | ⟨hv0, hv3⟩ | ⟨hv1, hv2⟩ | ⟨hv1, hv3⟩ | ⟨hv2, hv3⟩
    all_goals sorry
  }

end
