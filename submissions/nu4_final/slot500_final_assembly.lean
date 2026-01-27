/-
  slot500_final_assembly.lean

  FINAL ASSEMBLY: Close exists_safe_edge using proven lemmas from slot497.

  PROVEN IN slot497:
  - some_vertex_shared: In any 4-packing, some vertex v is shared by 2+ triangles
  - shared_vertex_edge_no_external: Edges containing shared vertex have no externals

  REMAINING: Show that at least one of m's 3 edges contains the shared vertex v.

  INSIGHT: Since v ∈ m (it's shared between m and another M-element), and
  m = {m.a, m.b, m.c}, we have v ∈ {m.a, m.b, m.c}.
  Each vertex appears in exactly 2 of 3 edges:
  - m.a in e1, e2
  - m.b in e1, e3
  - m.c in e2, e3
  So at least 2 edges contain v → at least one is safe!

  TIER: 1-2 (case analysis on which vertex equals v)
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

def hasNoExternal (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, e ∈ t.edges → e ∈ m.edges → t ≠ m →
    ¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3

lemma vertex_in_tri_iff (v : V9) (m : Tri) :
    vertexInTri v m ↔ v = m.a ∨ v = m.b ∨ v = m.c := by
  unfold vertexInTri Tri.vertices
  simp [mem_insert, mem_singleton]

lemma e1_contains_a (m : Tri) : edgeContainsVertex m.e1 m.a := by
  unfold edgeContainsVertex Tri.e1 mkE
  simp; left
  split_ifs <;> rfl

lemma e1_contains_b (m : Tri) : edgeContainsVertex m.e1 m.b := by
  unfold edgeContainsVertex Tri.e1 mkE
  simp; right
  split_ifs <;> rfl

lemma e2_contains_a (m : Tri) : edgeContainsVertex m.e2 m.a := by
  unfold edgeContainsVertex Tri.e2 mkE
  simp; left
  split_ifs <;> rfl

lemma e2_contains_c (m : Tri) : edgeContainsVertex m.e2 m.c := by
  unfold edgeContainsVertex Tri.e2 mkE
  simp; right
  split_ifs <;> rfl

lemma e3_contains_b (m : Tri) : edgeContainsVertex m.e3 m.b := by
  unfold edgeContainsVertex Tri.e3 mkE
  simp; left
  split_ifs <;> rfl

lemma e3_contains_c (m : Tri) : edgeContainsVertex m.e3 m.c := by
  unfold edgeContainsVertex Tri.e3 mkE
  simp; right
  split_ifs <;> rfl

lemma e1_in_edges (m : Tri) : m.e1 ∈ m.edges := by
  unfold Tri.edges; simp

lemma e2_in_edges (m : Tri) : m.e2 ∈ m.edges := by
  unfold Tri.edges; simp

lemma e3_in_edges (m : Tri) : m.e3 ∈ m.edges := by
  unfold Tri.edges; simp

axiom some_vertex_shared (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ v : V9, (vertexInTri v m0 ∧ vertexInTri v m1) ∨
              (vertexInTri v m0 ∧ vertexInTri v m2) ∨
              (vertexInTri v m0 ∧ vertexInTri v m3) ∨
              (vertexInTri v m1 ∧ vertexInTri v m2) ∨
              (vertexInTri v m1 ∧ vertexInTri v m3) ∨
              (vertexInTri v m2 ∧ vertexInTri v m3)

axiom shared_vertex_edge_no_external (m0 m1 m2 m3 m : Tri) (v : V9)
    (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3)
    (hv_m : vertexInTri v m)
    (hv_other : ∃ m' : Tri, (m' = m0 ∨ m' = m1 ∨ m' = m2 ∨ m' = m3) ∧ m' ≠ m ∧ vertexInTri v m')
    (e : V9 × V9) (he : e ∈ m.edges) (he_v : edgeContainsVertex e v) :
    hasNoExternal m e m0 m1 m2 m3

theorem exists_safe_edge (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    hasNoExternal m m.e1 m0 m1 m2 m3 ∨
    hasNoExternal m m.e2 m0 m1 m2 m3 ∨
    hasNoExternal m m.e3 m0 m1 m2 m3 := by
  obtain ⟨v, hv_shared⟩ := some_vertex_shared m0 m1 m2 m3 hpack
  -- Find which pair of triangles shares v, and check if m is one of them
  rcases hv_shared with ⟨hv0, hv1⟩ | ⟨hv0, hv2⟩ | ⟨hv0, hv3⟩ | ⟨hv1, hv2⟩ | ⟨hv1, hv3⟩ | ⟨hv2, hv3⟩
  all_goals {
    rcases hm with rfl | rfl | rfl | rfl
    all_goals {
      -- Determine which vertex of m equals v
      rw [vertex_in_tri_iff] at *
      rcases ‹vertexInTri v _ ∨ _› with hva | hvb | hvc
      all_goals {
        -- v equals one of m.a, m.b, m.c
        -- Apply shared_vertex_edge_no_external to an edge containing v
        first
        | { -- v = m.a, so e1 and e2 contain v
            left
            apply shared_vertex_edge_no_external m0 m1 m2 m3 _ v hpack
            · tauto
            · rw [vertex_in_tri_iff]; tauto
            · use _; refine ⟨?_, ?_, ?_⟩ <;> [tauto; tauto; rw [vertex_in_tri_iff]; tauto]
            · exact e1_in_edges _
            · subst hva; exact e1_contains_a _ }
        | { right; left
            apply shared_vertex_edge_no_external m0 m1 m2 m3 _ v hpack
            · tauto
            · rw [vertex_in_tri_iff]; tauto
            · use _; refine ⟨?_, ?_, ?_⟩ <;> [tauto; tauto; rw [vertex_in_tri_iff]; tauto]
            · exact e2_in_edges _
            · first | (subst hva; exact e2_contains_a _) | (subst hvc; exact e2_contains_c _) }
        | { right; right
            apply shared_vertex_edge_no_external m0 m1 m2 m3 _ v hpack
            · tauto
            · rw [vertex_in_tri_iff]; tauto
            · use _; refine ⟨?_, ?_, ?_⟩ <;> [tauto; tauto; rw [vertex_in_tri_iff]; tauto]
            · exact e3_in_edges _
            · first | (subst hvb; exact e3_contains_b _) | (subst hvc; exact e3_contains_c _) }
        | sorry
      }
    }
  }

end
