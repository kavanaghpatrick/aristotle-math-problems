/-
PATH_4 Configuration on Fin 9 for native_decide Testing

Structure: A—B—C—D where adjacent triangles share exactly 1 vertex
- A = {0, 1, 2}
- B = {2, 3, 4}  (A ∩ B = {2})
- C = {4, 5, 6}  (B ∩ C = {4})
- D = {6, 7, 8}  (C ∩ D = {6})

Non-adjacent pairs are disjoint:
- A ∩ C = ∅
- A ∩ D = ∅
- B ∩ D = ∅
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Path4Fin9

/-- The vertex type -/
abbrev V := Fin 9

/-- Triangle A: vertices 0, 1, 2 -/
def A : Finset V := {0, 1, 2}

/-- Triangle B: vertices 2, 3, 4 -/
def B : Finset V := {2, 3, 4}

/-- Triangle C: vertices 4, 5, 6 -/
def C : Finset V := {4, 5, 6}

/-- Triangle D: vertices 6, 7, 8 -/
def D : Finset V := {6, 7, 8}

/-- The shared vertices -/
def v1 : V := 2  -- A ∩ B
def v2 : V := 4  -- B ∩ C
def v3 : V := 6  -- C ∩ D

/-! ## Cardinality verification -/

theorem A_card : A.card = 3 := by native_decide
theorem B_card : B.card = 3 := by native_decide
theorem C_card : C.card = 3 := by native_decide
theorem D_card : D.card = 3 := by native_decide

/-! ## Adjacent pairs share exactly 1 vertex -/

theorem A_inter_B : A ∩ B = {v1} := by native_decide
theorem B_inter_C : B ∩ C = {v2} := by native_decide
theorem C_inter_D : C ∩ D = {v3} := by native_decide

theorem A_inter_B_card : (A ∩ B).card = 1 := by native_decide
theorem B_inter_C_card : (B ∩ C).card = 1 := by native_decide
theorem C_inter_D_card : (C ∩ D).card = 1 := by native_decide

/-! ## Non-adjacent pairs are disjoint -/

theorem A_inter_C : A ∩ C = ∅ := by native_decide
theorem A_inter_D : A ∩ D = ∅ := by native_decide
theorem B_inter_D : B ∩ D = ∅ := by native_decide

theorem A_C_disjoint : Disjoint A C := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  native_decide

theorem A_D_disjoint : Disjoint A D := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  native_decide

theorem B_D_disjoint : Disjoint B D := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  native_decide

/-! ## Shared vertices are in correct triangles -/

theorem v1_in_A : v1 ∈ A := by native_decide
theorem v1_in_B : v1 ∈ B := by native_decide
theorem v2_in_B : v2 ∈ B := by native_decide
theorem v2_in_C : v2 ∈ C := by native_decide
theorem v3_in_C : v3 ∈ C := by native_decide
theorem v3_in_D : v3 ∈ D := by native_decide

/-! ## Shared vertices are distinct -/

theorem shared_vertices_distinct : v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3 := by native_decide

/-! ## The SimpleGraph for PATH_4 -/

/-- Edge relation: vertices are adjacent iff they share a triangle -/
def path4Adj : V → V → Prop := fun u v =>
  u ≠ v ∧ ((u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) ∨ (u ∈ C ∧ v ∈ C) ∨ (u ∈ D ∧ v ∈ D))

instance : DecidableRel path4Adj := fun u v => by
  unfold path4Adj
  infer_instance

/-- The graph G containing exactly the edges of triangles A, B, C, D -/
def G : SimpleGraph V where
  Adj := path4Adj
  symm := by
    intro u v ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩
  loopless := by
    intro v ⟨hne, _⟩
    exact hne rfl

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel path4Adj)

/-! ## Verify triangles are cliques in G -/

/-- A set is a clique if all pairs of distinct vertices are adjacent -/
def isClique (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v

instance (s : Finset V) : Decidable (isClique s) := by
  unfold isClique
  infer_instance

theorem A_is_clique : isClique A := by native_decide
theorem B_is_clique : isClique B := by native_decide
theorem C_is_clique : isClique C := by native_decide
theorem D_is_clique : isClique D := by native_decide

/-! ## The 4 triangles form a valid packing (pairwise edge-disjoint) -/

/-- Edges of a triangle -/
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.sym2.filter (fun e => ¬e.IsDiag)

/-- Edge-disjoint triangles -/
def edgeDisjoint (t1 t2 : Finset V) : Prop :=
  Disjoint (triangleEdges t1) (triangleEdges t2)

instance (t1 t2 : Finset V) : Decidable (edgeDisjoint t1 t2) := by
  unfold edgeDisjoint triangleEdges
  infer_instance

theorem A_B_edge_disjoint : edgeDisjoint A B := by native_decide
theorem A_C_edge_disjoint : edgeDisjoint A C := by native_decide
theorem A_D_edge_disjoint : edgeDisjoint A D := by native_decide
theorem B_C_edge_disjoint : edgeDisjoint B C := by native_decide
theorem B_D_edge_disjoint : edgeDisjoint B D := by native_decide
theorem C_D_edge_disjoint : edgeDisjoint C D := by native_decide

/-! ## Packing structure -/

/-- The packing as a set of triangles -/
def packing : Finset (Finset V) := {A, B, C, D}

theorem packing_card : packing.card = 4 := by native_decide

/-- All triangles in packing have 3 vertices -/
theorem packing_all_triangles : ∀ t ∈ packing, t.card = 3 := by
  intro t ht
  simp only [packing, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact A_card
  · exact B_card
  · exact C_card
  · exact D_card

/-! ## Union of all vertices -/

def allVertices : Finset V := A ∪ B ∪ C ∪ D

theorem allVertices_eq : allVertices = {0, 1, 2, 3, 4, 5, 6, 7, 8} := by native_decide

theorem allVertices_card : allVertices.card = 9 := by native_decide

/-! ## PATH_4 structure verification -/

/-- PATH_4 configuration: A linear chain of 4 triangles -/
structure IsPath4 (t1 t2 t3 t4 : Finset V) : Prop where
  card1 : t1.card = 3
  card2 : t2.card = 3
  card3 : t3.card = 3
  card4 : t4.card = 3
  adj_12 : (t1 ∩ t2).card = 1
  adj_23 : (t2 ∩ t3).card = 1
  adj_34 : (t3 ∩ t4).card = 1
  disj_13 : t1 ∩ t3 = ∅
  disj_14 : t1 ∩ t4 = ∅
  disj_24 : t2 ∩ t4 = ∅

theorem path4_valid : IsPath4 A B C D where
  card1 := A_card
  card2 := B_card
  card3 := C_card
  card4 := D_card
  adj_12 := A_inter_B_card
  adj_23 := B_inter_C_card
  adj_34 := C_inter_D_card
  disj_13 := A_inter_C
  disj_14 := A_inter_D
  disj_24 := B_inter_D

/-! ## Cover analysis for τ ≤ 8 -/

/-- Edges of the graph (all triangle edges) -/
def graphEdges : Finset (Sym2 V) :=
  triangleEdges A ∪ triangleEdges B ∪ triangleEdges C ∪ triangleEdges D

theorem graphEdges_card : graphEdges.card = 12 := by native_decide

/-- A proposed 8-edge cover using 2 edges from each triangle -/

-- From A: edges {0,1} and {1,2}
def coverA : Finset (Sym2 V) := {s(0, 1), s(1, 2)}

-- From B: edges {2,3} and {3,4}
def coverB : Finset (Sym2 V) := {s(2, 3), s(3, 4)}

-- From C: edges {4,5} and {5,6}
def coverC : Finset (Sym2 V) := {s(4, 5), s(5, 6)}

-- From D: edges {6,7} and {7,8}
def coverD : Finset (Sym2 V) := {s(6, 7), s(7, 8)}

def cover8 : Finset (Sym2 V) := coverA ∪ coverB ∪ coverC ∪ coverD

theorem cover8_card : cover8.card = 8 := by native_decide

/-- Each triangle is hit by the cover -/
def triangleHitBy (t : Finset V) (E : Finset (Sym2 V)) : Prop :=
  ∃ e ∈ E, ∃ u v, e = s(u, v) ∧ u ∈ t ∧ v ∈ t ∧ u ≠ v

instance (t : Finset V) (E : Finset (Sym2 V)) : Decidable (triangleHitBy t E) := by
  unfold triangleHitBy
  infer_instance

-- Direct check that each triangle shares an edge with cover8
theorem A_hit : (triangleEdges A ∩ cover8).Nonempty := by native_decide
theorem B_hit : (triangleEdges B ∩ cover8).Nonempty := by native_decide
theorem C_hit : (triangleEdges C ∩ cover8).Nonempty := by native_decide
theorem D_hit : (triangleEdges D ∩ cover8).Nonempty := by native_decide

/-! ## Summary theorem -/

/-- The PATH_4 configuration on Fin 9 with an 8-edge cover -/
theorem path4_fin9_summary :
    IsPath4 A B C D ∧
    packing.card = 4 ∧
    cover8.card = 8 ∧
    (triangleEdges A ∩ cover8).Nonempty ∧
    (triangleEdges B ∩ cover8).Nonempty ∧
    (triangleEdges C ∩ cover8).Nonempty ∧
    (triangleEdges D ∩ cover8).Nonempty :=
  ⟨path4_valid, packing_card, cover8_card, A_hit, B_hit, C_hit, D_hit⟩

end Path4Fin9
