/-
  slot499_general_safe_edge.lean

  GENERALIZES slot498: exists_safe_edge for ALL 4-packings on Fin 9.

  KEY INSIGHT from slot498:
  - In star configuration, edges containing the shared vertex have no externals
  - Because any external triangle containing that edge would also contain the shared vertex
  - And thus share an edge with another M-element containing that vertex

  GENERALIZATION:
  - Any 4-packing on Fin 9 has 12 vertex-triangle incidences
  - By pigeonhole (9 vertices), some vertex v is in 2+ triangles
  - Edges of one triangle containing v have restricted externals
  - This gives exists_safe_edge

  TIER: 2 (generalize proven concrete case)
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

def vertexInTri (v : V9) (t : Tri) : Prop := v ∈ t.vertices

instance (v : V9) (t : Tri) : Decidable (vertexInTri v t) :=
  inferInstanceAs (Decidable (_ ∈ _))

def edgeContainsVertex (e : V9 × V9) (v : V9) : Prop := e.1 = v ∨ e.2 = v

instance (e : V9 × V9) (v : V9) : Decidable (edgeContainsVertex e v) :=
  inferInstanceAs (Decidable (_ ∨ _))

def isExternal (t m m0 m1 m2 m3 : Tri) (e : V9 × V9) : Prop :=
  e ∈ t.edges ∧ e ∈ m.edges ∧ t ≠ m ∧
  edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

instance (t m m0 m1 m2 m3 : Tri) (e : V9 × V9) : Decidable (isExternal t m m0 m1 m2 m3 e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def edgeSafeToRemove (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, ¬isExternal t m m0 m1 m2 m3 e

lemma edge_containing_shared_vertex_safe (m0 m1 m2 m3 m m' : Tri) (v : V9)
    (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3)
    (hm' : m' = m0 ∨ m' = m1 ∨ m' = m2 ∨ m' = m3)
    (hm_ne : m ≠ m')
    (hv_m : vertexInTri v m)
    (hv_m' : vertexInTri v m')
    (e : V9 × V9) (he : e ∈ m.edges) (he_v : edgeContainsVertex e v) :
    edgeSafeToRemove m e m0 m1 m2 m3 := by
  intro t
  unfold isExternal
  intro ⟨ht_e, ht_m, ht_ne, ht_m0_disj, ht_m1_disj, ht_m2_disj, ht_m3_disj⟩
  -- t contains edge e, which contains vertex v
  -- t is a triangle containing v
  -- m' also contains v
  -- Since t contains edge e which contains v, t contains v
  -- t and m' both contain v
  -- If t also contains another vertex of m' (call it w), then t shares edge (v,w) with m'
  -- Since e contains v and e ∈ m.edges, and m ≠ m', we have e ∉ m'.edges (edge-disjoint packing)
  -- So t's edge e is not in m'
  -- But t might have another edge containing v that IS in m'
  -- For t to be external (disjoint from m'), t cannot share any edge with m'
  -- But t contains v, and m' contains v
  -- m' has 2 edges containing v (say (v, w1) and (v, w2) where m' = {v, w1, w2})
  -- t = {t.a, t.b, t.c} with v ∈ {t.a, t.b, t.c}
  -- WLOG say v = t.a. Then t has edges (v, t.b) and (v, t.c)
  -- For t to be edge-disjoint from m', both (v, t.b) and (v, t.c) must NOT be in m'.edges
  -- m'.edges = {(v,w1), (v,w2), (w1,w2)}
  -- So t.b, t.c ∉ {w1, w2}
  -- But there are only 9 vertices, and m = {m.a, m.b, m.c}, m' = {v, w1, w2}
  -- t shares edge e with m, where e contains v
  -- Say e = (v, m.b) (one of m's edges containing v)
  -- Then t.b or t.c equals m.b (the other endpoint of e)
  -- The remaining vertex of t (call it x) satisfies x ∉ {v, m.b}
  -- For t to be disjoint from m', x ∉ {w1, w2}
  -- This constrains x to V9 \ {v, m.b, w1, w2} which has 9-4 = 5 vertices
  -- But wait, we also need e ∈ t.edges, which forces certain constraints
  -- Actually, the key is: t contains v, and t is disjoint from m' which also contains v
  -- Since m' contains v and has 2 other vertices w1, w2
  -- t must not share any of (v,w1), (v,w2), (w1,w2) with m'
  -- But t contains v, so t has 2 edges containing v
  -- Call them (v, x) and (v, y) where {v, x, y} = t
  -- For neither to be in m'.edges = {(v,w1), (v,w2), (w1,w2)}:
  -- x ∉ {w1, w2} and y ∉ {w1, w2}
  -- So {x, y} ∩ {w1, w2} = ∅
  -- Also, (x,y) ∉ {(w1,w2)} means {x,y} ≠ {w1,w2}
  -- Which is implied by x,y ∉ {w1,w2}
  -- Now, we also need e ∈ t.edges and e ∈ m.edges
  -- e contains v (given), so e = (v, z) for some z ∈ m.vertices, z ≠ v
  -- And e ∈ t.edges, so z ∈ {x, y}
  -- So far consistent: t = {v, x, y} with e = (v, z), z ∈ {x, y}
  -- The constraint is: x, y ∉ {w1, w2}
  -- But this IS possible! There are 9 - 1 - 2 = 6 choices for {x,y} from V9 \ {v, w1, w2}
  -- Wait, but we haven't used the full constraints yet
  -- The external constraint says t is disjoint from ALL of m0, m1, m2, m3
  -- In particular, t is disjoint from m' (one of them)
  -- But t contains v which is also in m'!
  -- Hmm, wait. edgeDisj means edge-disjoint, not vertex-disjoint
  -- So t can share vertex v with m' as long as they don't share an edge
  -- The slot498 proof used a different argument: it showed that sharing vertex v
  -- with m' forces t to share an edge with m' (if the other vertices of t are "too close" to m')
  -- This works in the star configuration because ALL other vertices are "close" to vertex 0
  sorry

theorem exists_safe_edge (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    edgeSafeToRemove m m.e1 m0 m1 m2 m3 ∨
    edgeSafeToRemove m m.e2 m0 m1 m2 m3 ∨
    edgeSafeToRemove m m.e3 m0 m1 m2 m3 := by
  -- By pigeonhole, some vertex v is in 2+ triangles of M
  -- Edges of m containing v have restricted externals
  -- Use edge_containing_shared_vertex_safe for such edges
  sorry

end
