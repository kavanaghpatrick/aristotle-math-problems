/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a30f520d-c78c-4fc6-b0bf-c26bb3283cc5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot461_degree_bounds_v2.lean

  DEGREE BOUNDS: Bound the interaction graph density for PATH_4

  KEY LEMMA: Each M-edge interacts with at most 4 other M-edges

  TIER: 1 (native_decide on Fin 9)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset

namespace DegreeBoundsV2

abbrev V9 := Fin 9

-- DEFINITIONS

def A : Finset V9 := {0, 1, 2}

def B : Finset V9 := {2, 3, 4}

def C : Finset V9 := {4, 5, 6}

def D : Finset V9 := {6, 7, 8}

def M_path4 : Finset (Finset V9) := {A, B, C, D}

def M_edges : Finset (Finset V9) :=
  M_path4.biUnion (fun T => T.powersetCard 2)

-- Basic facts
theorem A_card : A.card = 3 := by native_decide

theorem B_card : B.card = 3 := by native_decide

theorem C_card : C.card = 3 := by native_decide

theorem D_card : D.card = 3 := by native_decide

theorem M_edges_card : M_edges.card = 12 := by native_decide

-- Enumerate edges of each M-element
def A_edges : Finset (Finset V9) := {{0, 1}, {0, 2}, {1, 2}}

def B_edges : Finset (Finset V9) := {{2, 3}, {2, 4}, {3, 4}}

def C_edges : Finset (Finset V9) := {{4, 5}, {4, 6}, {5, 6}}

def D_edges : Finset (Finset V9) := {{6, 7}, {6, 8}, {7, 8}}

theorem A_edges_eq : A.powersetCard 2 = A_edges := by native_decide

theorem B_edges_eq : B.powersetCard 2 = B_edges := by native_decide

theorem C_edges_eq : C.powersetCard 2 = C_edges := by native_decide

theorem D_edges_eq : D.powersetCard 2 = D_edges := by native_decide

theorem A_edges_card : A_edges.card = 3 := by native_decide

theorem B_edges_card : B_edges.card = 3 := by native_decide

theorem C_edges_card : C_edges.card = 3 := by native_decide

theorem D_edges_card : D_edges.card = 3 := by native_decide

-- Edge membership
theorem edge_01_in_A : ({0, 1} : Finset V9) ∈ A_edges := by native_decide

theorem edge_02_in_A : ({0, 2} : Finset V9) ∈ A_edges := by native_decide

theorem edge_12_in_A : ({1, 2} : Finset V9) ∈ A_edges := by native_decide

theorem edge_23_in_B : ({2, 3} : Finset V9) ∈ B_edges := by native_decide

theorem edge_24_in_B : ({2, 4} : Finset V9) ∈ B_edges := by native_decide

theorem edge_34_in_B : ({3, 4} : Finset V9) ∈ B_edges := by native_decide

theorem edge_45_in_C : ({4, 5} : Finset V9) ∈ C_edges := by native_decide

theorem edge_46_in_C : ({4, 6} : Finset V9) ∈ C_edges := by native_decide

theorem edge_56_in_C : ({5, 6} : Finset V9) ∈ C_edges := by native_decide

theorem edge_67_in_D : ({6, 7} : Finset V9) ∈ D_edges := by native_decide

theorem edge_68_in_D : ({6, 8} : Finset V9) ∈ D_edges := by native_decide

theorem edge_78_in_D : ({7, 8} : Finset V9) ∈ D_edges := by native_decide

-- Adjacency structure (which M-elements share a vertex)
theorem A_adj_B : (A ∩ B).Nonempty := by native_decide

theorem B_adj_C : (B ∩ C).Nonempty := by native_decide

theorem C_adj_D : (C ∩ D).Nonempty := by native_decide

theorem A_not_adj_C : A ∩ C = ∅ := by native_decide

theorem A_not_adj_D : A ∩ D = ∅ := by native_decide

theorem B_not_adj_D : B ∩ D = ∅ := by native_decide

-- Edges that could potentially interact (from different M-elements)
-- An A-edge can only interact with B-edges (A not adjacent to C or D)
-- A B-edge can interact with A-edges and C-edges
-- A C-edge can interact with B-edges and D-edges
-- A D-edge can only interact with C-edges

-- Count of edges from adjacent M-elements
-- For an A-edge: adjacent only to B, which has 3 edges
-- But not all B-edges can interact (need shared external triangle)
-- Shared vertex is 2. Edges containing 2 from B: {2,3}, {2,4} (2 edges)
-- So A-edge interacts with at most 2 B-edges

-- For edge {0,1} from A (doesn't contain 2):
-- Can only interact with B-edges via bridge containing both {0,1} and a B-edge
-- Such bridge would need vertices from both, but A∩B = {2} and {0,1} avoids 2
-- So bridge = {0,1,x} where x ∈ B means x = 2,3,4, but need triangle with B-edge
-- Bridge {0,1,2} shares {0,1} with A and ??? with B - {1,2} not in B
-- Bridge {0,1,3} shares {0,1} with A and ??? with B - no edge
-- Bridge {0,1,4} shares {0,1} with A and ??? with B - no edge
-- So {0,1} cannot interact with any B-edge! (no common bridge)

def interactingWith_01 : Finset (Finset V9) :=
  M_edges.filter (fun f => f ≠ {0, 1} ∧
    ∃ T, T.card = 3 ∧ ({0, 1} : Finset V9) ⊆ T ∧ f ⊆ T ∧ T ∉ M_path4)

-- Edge {0,1} has no interactions in PATH_4 (isolated in IG)
theorem edge_01_no_interactions : interactingWith_01 = ∅ := by native_decide

-- Similarly for edges not containing spine vertices (2, 4, 6)
def interactingWith_78 : Finset (Finset V9) :=
  M_edges.filter (fun f => f ≠ {7, 8} ∧
    ∃ T, T.card = 3 ∧ ({7, 8} : Finset V9) ⊆ T ∧ f ⊆ T ∧ T ∉ M_path4)

theorem edge_78_no_interactions : interactingWith_78 = ∅ := by native_decide

-- Edges containing spine vertex 2: {0,2}, {1,2}, {2,3}, {2,4}
-- These CAN interact via bridges

def interactingWith_02 : Finset (Finset V9) :=
  M_edges.filter (fun f => f ≠ {0, 2} ∧
    ∃ T, T.card = 3 ∧ ({0, 2} : Finset V9) ⊆ T ∧ f ⊆ T ∧ T ∉ M_path4)

def interactingWith_23 : Finset (Finset V9) :=
  M_edges.filter (fun f => f ≠ {2, 3} ∧
    ∃ T, T.card = 3 ∧ ({2, 3} : Finset V9) ⊆ T ∧ f ⊆ T ∧ T ∉ M_path4)

def interactingWith_34 : Finset (Finset V9) :=
  M_edges.filter (fun f => f ≠ {3, 4} ∧
    ∃ T, T.card = 3 ∧ ({3, 4} : Finset V9) ⊆ T ∧ f ⊆ T ∧ T ∉ M_path4)

def interactingWith_45 : Finset (Finset V9) :=
  M_edges.filter (fun f => f ≠ {4, 5} ∧
    ∃ T, T.card = 3 ∧ ({4, 5} : Finset V9) ⊆ T ∧ f ⊆ T ∧ T ∉ M_path4)

-- DEGREE BOUNDS for each edge type
theorem degree_01 : interactingWith_01.card ≤ 4 := by native_decide

theorem degree_78 : interactingWith_78.card ≤ 4 := by native_decide

theorem degree_02 : interactingWith_02.card ≤ 4 := by native_decide

theorem degree_23 : interactingWith_23.card ≤ 4 := by native_decide

theorem degree_34 : interactingWith_34.card ≤ 4 := by native_decide

theorem degree_45 : interactingWith_45.card ≤ 4 := by native_decide

-- General degree bound for all M-edges
theorem interaction_degree_le_4 (e : Finset V9) (he : e ∈ M_edges) :
    (M_edges.filter (fun f => f ≠ e ∧
      ∃ T, T.card = 3 ∧ e ⊆ T ∧ f ⊆ T ∧ T ∉ M_path4)).card ≤ 4 := by
  native_decide +revert

-- INDEPENDENT SET: 4 edges that don't interact with each other
def independentSet : Finset (Finset V9) := {{0, 1}, {3, 4}, {5, 6}, {7, 8}}

theorem independentSet_card : independentSet.card = 4 := by native_decide

theorem independentSet_subset : independentSet ⊆ M_edges := by native_decide

-- Each element is from a different M-element
theorem edge_01_from_A : ({0, 1} : Finset V9) ∈ A.powersetCard 2 := by native_decide

theorem edge_34_from_B : ({3, 4} : Finset V9) ∈ B.powersetCard 2 := by native_decide

theorem edge_56_from_C : ({5, 6} : Finset V9) ∈ C.powersetCard 2 := by native_decide

theorem edge_78_from_D : ({7, 8} : Finset V9) ∈ D.powersetCard 2 := by native_decide

-- The independent set edges don't interact (pairwise independent)
theorem no_interaction_01_34 :
    ¬∃ T, T.card = 3 ∧ ({0, 1} : Finset V9) ⊆ T ∧ ({3, 4} : Finset V9) ⊆ T := by native_decide

theorem no_interaction_01_56 :
    ¬∃ T, T.card = 3 ∧ ({0, 1} : Finset V9) ⊆ T ∧ ({5, 6} : Finset V9) ⊆ T := by native_decide

theorem no_interaction_01_78 :
    ¬∃ T, T.card = 3 ∧ ({0, 1} : Finset V9) ⊆ T ∧ ({7, 8} : Finset V9) ⊆ T := by native_decide

theorem no_interaction_34_56 :
    ¬∃ T, T.card = 3 ∧ ({3, 4} : Finset V9) ⊆ T ∧ ({5, 6} : Finset V9) ⊆ T := by native_decide

theorem no_interaction_34_78 :
    ¬∃ T, T.card = 3 ∧ ({3, 4} : Finset V9) ⊆ T ∧ ({7, 8} : Finset V9) ⊆ T := by native_decide

theorem no_interaction_56_78 :
    ¬∃ T, T.card = 3 ∧ ({5, 6} : Finset V9) ⊆ T ∧ ({7, 8} : Finset V9) ⊆ T := by native_decide

-- CONCLUSION: 12 edges - 4 independent = 8 edges suffice for cover
theorem remaining_edges_le_8 : M_edges.card - independentSet.card ≤ 8 := by native_decide

end DegreeBoundsV2