/-
  slot502_tau_le_8_assembly.lean

  FINAL ASSEMBLY: τ ≤ 8 for ν = 4 on Fin 9.

  KEY RESULTS FROM PRIOR SLOTS:
  - slot501: exists_safe_edge PROVEN - ALL edges of ALL M-elements have no externals
  - slot496: all_M_edges_cover - 12 M-edges cover all triangles

  INSIGHT FOR τ ≤ 8:
  Since all edges are "safe" (no externals), every triangle T sharing edge e with
  some M-element m is covered by edge e.

  The question is: can we select only 2 edges per M-element?

  The key is the shared vertex argument:
  - Some vertex v is shared by two M-elements mi and mj
  - mi and mj together have 4 edges containing v
  - Select these 4 edges (2 per triangle containing v)
  - For the other 2 M-elements mk, ml: select any 2 edges each

  Total: 2 + 2 + 2 + 2 = 8 edges

  TIER: 2 (structural combination of proven lemmas)
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

def sharesEdge (t m : Tri) : Prop := ¬edgeDisj t m

instance (t m : Tri) : Decidable (sharesEdge t m) :=
  inferInstanceAs (Decidable (¬edgeDisj t m))

-- Definition of covering
def covers (E : Finset (V9 × V9)) (t : Tri) : Prop :=
  ∃ e ∈ E, e ∈ t.edges

def coversAll (E : Finset (V9 × V9)) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, (sharesEdge t m0 ∨ sharesEdge t m1 ∨ sharesEdge t m2 ∨ sharesEdge t m3) →
    covers E t

-- Key lemma: triangle sharing edge e with m is covered by e
lemma edge_covers_sharing_triangle (t m : Tri) (e : V9 × V9)
    (he_m : e ∈ m.edges) (hshare : e ∈ t.edges) :
    covers {e} t := by
  use e
  simp [hshare]

-- Key lemma: if t shares an edge with m, some edge of m is in t
lemma sharing_means_common_edge (t m : Tri) (h : sharesEdge t m) :
    ∃ e ∈ m.edges, e ∈ t.edges := by
  unfold sharesEdge edgeDisj at h
  simp only [Set.not_disjoint_iff] at h
  obtain ⟨e, he_t, he_m⟩ := h
  exact ⟨e, he_m, he_t⟩

-- The 12 M-edges cover all triangles sharing with M
lemma M_edges_cover_all (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    coversAll (m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges) m0 m1 m2 m3 := by
  intro t ht
  rcases ht with h0 | h1 | h2 | h3
  · obtain ⟨e, he_m, he_t⟩ := sharing_means_common_edge t m0 h0
    exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_left _ he_m)), he_t⟩
  · obtain ⟨e, he_m, he_t⟩ := sharing_means_common_edge t m1 h1
    exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_right _ he_m)), he_t⟩
  · obtain ⟨e, he_m, he_t⟩ := sharing_means_common_edge t m2 h2
    exact ⟨e, mem_union_left _ (mem_union_right _ he_m), he_t⟩
  · obtain ⟨e, he_m, he_t⟩ := sharing_means_common_edge t m3 h3
    exact ⟨e, mem_union_right _ he_m, he_t⟩

-- The union of 4 triangles' edges has at most 12 elements
lemma M_edges_card_le_12 (m0 m1 m2 m3 : Tri) :
    (m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges).card ≤ 12 := by
  have h0 : m0.edges.card ≤ 3 := by unfold Tri.edges; simp
  have h1 : m1.edges.card ≤ 3 := by unfold Tri.edges; simp
  have h2 : m2.edges.card ≤ 3 := by unfold Tri.edges; simp
  have h3 : m3.edges.card ≤ 3 := by unfold Tri.edges; simp
  calc (m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges).card
      ≤ m0.edges.card + m1.edges.card + m2.edges.card + m3.edges.card := by
        apply le_trans (card_union_le _ _)
        apply add_le_add_right
        apply le_trans (card_union_le _ _)
        apply add_le_add_right
        exact card_union_le _ _
    _ ≤ 3 + 3 + 3 + 3 := by omega
    _ = 12 := by ring

-- τ ≤ 12 (baseline result)
theorem tau_le_12 (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ E : Finset (V9 × V9), E.card ≤ 12 ∧ coversAll E m0 m1 m2 m3 := by
  use m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges
  constructor
  · exact M_edges_card_le_12 m0 m1 m2 m3
  · exact M_edges_cover_all m0 m1 m2 m3 hpack

/-
  PROOF SKETCH FOR τ ≤ 8:

  1. By pigeonhole (12 vertex-incidences into 9 vertices), some vertex v is shared
     by two M-elements mi and mj.

  2. mi has edges: (v,a1), (v,a2), (a1,a2) where mi = {v, a1, a2}
     mj has edges: (v,b1), (v,b2), (b1,b2) where mj = {v, b1, b2}

  3. Select from mi: (v,a1), (v,a2) (the 2 edges containing v)
     Select from mj: (v,b1), (v,b2) (the 2 edges containing v)
     Select from mk: any 2 edges
     Select from ml: any 2 edges

  4. Total: 8 edges. Need to show these cover all triangles.

  5. Any triangle T sharing edge with M:
     - If T shares edge with mi or mj that contains v: covered by our selection
     - If T shares only (a1,a2) with mi (and nothing else with any M-element):
       * Then T = {a1, a2, x} with x ≠ v, x ∉ {b1, b2}
       * T must share an edge with mk or ml (by maximality argument)
       * Our selection from mk or ml covers T

  The tricky part is step 5. Let Aristotle handle the case analysis.
-/

-- Vertex in triangle predicate
def vertexInTri (v : V9) (t : Tri) : Prop := v ∈ t.vertices

instance (v : V9) (t : Tri) : Decidable (vertexInTri v t) :=
  inferInstanceAs (Decidable (_ ∈ _))

-- Edges containing a specific vertex
def edgesContainingVertex (t : Tri) (v : V9) : Finset (V9 × V9) :=
  t.edges.filter (fun e => e.1 = v ∨ e.2 = v)

-- Selection of 2 edges per M-element
def select2Edges (m : Tri) : Finset (V9 × V9) := {m.e1, m.e2}

-- Alternative selection for M-elements containing shared vertex
def select2EdgesContainingV (m : Tri) (v : V9) (hv : vertexInTri v m) : Finset (V9 × V9) :=
  edgesContainingVertex m v

lemma select2Edges_card (m : Tri) : (select2Edges m).card ≤ 2 := by
  unfold select2Edges
  simp

lemma select2Edges_subset (m : Tri) : select2Edges m ⊆ m.edges := by
  unfold select2Edges Tri.edges
  intro e he
  simp at he ⊢
  tauto

-- The key theorem: τ ≤ 8
-- We construct an 8-edge cover by selecting 2 edges from each M-element
theorem tau_le_8 (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ E : Finset (V9 × V9), E.card ≤ 8 ∧ coversAll E m0 m1 m2 m3 := by
  -- Select 2 edges from each M-element
  let E := select2Edges m0 ∪ select2Edges m1 ∪ select2Edges m2 ∪ select2Edges m3
  use E
  constructor
  · -- E.card ≤ 8
    calc E.card
        ≤ (select2Edges m0).card + (select2Edges m1).card +
          (select2Edges m2).card + (select2Edges m3).card := by
          apply le_trans (card_union_le _ _)
          apply add_le_add_right
          apply le_trans (card_union_le _ _)
          apply add_le_add_right
          exact card_union_le _ _
      _ ≤ 2 + 2 + 2 + 2 := by
          apply add_le_add
          apply add_le_add
          apply add_le_add
          exact select2Edges_card m0
          exact select2Edges_card m1
          exact select2Edges_card m2
          exact select2Edges_card m3
      _ = 8 := by ring
  · -- coversAll E m0 m1 m2 m3
    intro t ht
    -- t shares an edge with some M-element
    rcases ht with h0 | h1 | h2 | h3
    all_goals {
      obtain ⟨e, he_m, he_t⟩ := sharing_means_common_edge t _ ‹_›
      -- e is the shared edge
      -- If e is in our selection, we're done
      -- If e is the third edge (not selected), need to argue t shares another edge
      -- with a different M-element that IS selected
      -- For now, use the fact that e1 and e2 are always selected
      unfold select2Edges Tri.edges at *
      simp at *
      first
      | { -- e is e1 or e2 of the M-element
          rcases he_m with rfl | rfl | rfl
          · -- e = m.e1, which is selected
            use e
            simp [he_t]
          · -- e = m.e2, which is selected
            use e
            simp [he_t]
          · -- e = m.e3, NOT selected - need more careful argument
            sorry
        }
    }
