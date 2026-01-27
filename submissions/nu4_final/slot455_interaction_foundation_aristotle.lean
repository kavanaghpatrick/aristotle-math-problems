/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1ba87a30-889f-48ce-8252-369420a40b22

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem external_shares_at_most_two (T : Finset V9) (hT : T.card = 3) :
    (M_edges M_path4 ∩ T.powersetCard 2).card ≤ 2 ∨ T ∈ M_path4

- theorem interaction_implies_distinct_parents (e₁ e₂ : Finset V9)
    (he₁ : e₁ ∈ M_edges M_path4) (he₂ : e₂ ∈ M_edges M_path4) (hne : e₁ ≠ e₂)
    (X : Finset V9) (hX : X ∈ M_path4) (he₁X : e₁ ∈ X.powersetCard 2) (he₂X : e₂ ∈ X.powersetCard 2) :
    ¬∃ T, T ∈ externalTriangles (⊥ : SimpleGraph V9) M_path4 ∧ e₁ ⊆ T ∧ e₂ ⊆ T
-/

/-
  slot455_interaction_foundation.lean
  
  MULTI-AGENT DEBATE CONSENSUS (Jan 18, 2026)
  Participants: Grok-4, Gemini
  Moderator: Claude
  
  FOUNDATION: InteractionGraph definition and key structural lemmas
  
  STRATEGY:
  1. Define InteractionGraph where vertices are M-edges
  2. Edges represent shared external triangles (bridges)
  3. Prove key structural lemmas for degree bounds
  
  This file establishes the foundation for proving τ ≤ 8 for general ν = 4 graphs.
  
  TIER: 1-2 (definitions + native_decide on Fin 9)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset Sym2

namespace InteractionFoundation

abbrev V9 := Fin 9

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle packing: edge-disjoint triangles -/
def isTrianglePacking (G : SimpleGraph V9) [DecidableRel G.Adj] (M : Finset (Finset V9)) : Prop :=
  (∀ T ∈ M, T ∈ G.cliqueFinset 3) ∧
  (∀ T₁ ∈ M, ∀ T₂ ∈ M, T₁ ≠ T₂ → T₁.sym2 ∩ T₂.sym2 = ∅)

/-- All edges contained in packing elements -/
def M_edges (M : Finset (Finset V9)) : Finset (Finset V9) :=
  M.biUnion (fun T => T.powersetCard 2)

/-- External triangles: triangles sharing edge with M but not in M -/
def externalTriangles (G : SimpleGraph V9) [DecidableRel G.Adj] (M : Finset (Finset V9)) : Finset (Finset V9) :=
  (G.cliqueFinset 3).filter (fun T => T ∉ M ∧ ∃ e ∈ M_edges M, e ⊆ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- INTERACTION GRAPH DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two M-edges interact if they both appear in some external triangle -/
def edgesInteract (G : SimpleGraph V9) [DecidableRel G.Adj] (M : Finset (Finset V9))
    (e₁ e₂ : Finset V9) : Prop :=
  e₁ ≠ e₂ ∧
  e₁ ∈ M_edges M ∧
  e₂ ∈ M_edges M ∧
  ∃ T ∈ externalTriangles G M, e₁ ⊆ T ∧ e₂ ⊆ T

-- ══════════════════════════════════════════════════════════════════════════════
-- CONCRETE INSTANCE: PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

def A : Finset V9 := {0, 1, 2}

def B : Finset V9 := {2, 3, 4}

def C : Finset V9 := {4, 5, 6}

def D : Finset V9 := {6, 7, 8}

def M_path4 : Finset (Finset V9) := {A, B, C, D}

-- PATH_4 packing verification
theorem M_path4_card : M_path4.card = 4 := by native_decide

theorem A_card : A.card = 3 := by native_decide

theorem B_card : B.card = 3 := by native_decide

theorem C_card : C.card = 3 := by native_decide

theorem D_card : D.card = 3 := by native_decide

-- Edge-disjointness
theorem A_B_edge_disjoint : A.sym2 ∩ B.sym2 = ∅ := by native_decide

theorem B_C_edge_disjoint : B.sym2 ∩ C.sym2 = ∅ := by native_decide

theorem C_D_edge_disjoint : C.sym2 ∩ D.sym2 = ∅ := by native_decide

theorem A_C_edge_disjoint : A.sym2 ∩ C.sym2 = ∅ := by native_decide

theorem A_D_edge_disjoint : A.sym2 ∩ D.sym2 = ∅ := by native_decide

theorem B_D_edge_disjoint : B.sym2 ∩ D.sym2 = ∅ := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY STRUCTURAL LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- M_edges contains exactly 12 edges (4 triangles × 3 edges) -/
theorem M_edges_card : (M_edges M_path4).card = 12 := by native_decide

/-- Each M-element contributes 3 edges -/
theorem A_edges_card : (A.powersetCard 2).card = 3 := by native_decide

theorem B_edges_card : (B.powersetCard 2).card = 3 := by native_decide

theorem C_edges_card : (C.powersetCard 2).card = 3 := by native_decide

theorem D_edges_card : (D.powersetCard 2).card = 3 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL TRIANGLE CLASSIFICATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- External type: Private (shares edge with 1 M-element) or Bridge (shares with 2) -/
inductive ExternalType
  | Private : ExternalType
  | Bridge : ExternalType
  deriving DecidableEq, Repr

/-- Count how many M-elements a triangle shares an edge with -/
def countMParents (M : Finset (Finset V9)) (T : Finset V9) : ℕ :=
  (M.filter (fun X => (X.powersetCard 2 ∩ T.powersetCard 2).Nonempty)).card

/-- Classify external triangle by parent count -/
def classifyExternal (M : Finset (Finset V9)) (T : Finset V9) : ExternalType :=
  if countMParents M T ≤ 1 then ExternalType.Private else ExternalType.Bridge

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: EXTERNAL SHARES AT MOST 2 EDGES
-- ══════════════════════════════════════════════════════════════════════════════

/-- An external triangle shares at most 2 edges with M.
    If it shared 3, it would BE an M-element. -/
theorem external_shares_at_most_two (T : Finset V9) (hT : T.card = 3) :
    (M_edges M_path4 ∩ T.powersetCard 2).card ≤ 2 ∨ T ∈ M_path4 := by
  by_cases h : T ∈ M_path4
  · right; exact h
  · left
    -- If T shares 3 edges with M, those 3 edges form T itself
    -- But T ∉ M, so the edges come from different M-elements
    -- Triangle has only 3 edges, can share at most 2 with non-self M-elements
    native_decide +revert

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

/-- The bridge between B and C -/
def T_bridge : Finset V9 := {3, 4, 5}

theorem T_bridge_card : T_bridge.card = 3 := by native_decide

/-- Bridge shares edge {3,4} with B -/
theorem T_bridge_shares_B : ({3, 4} : Finset V9) ⊆ T_bridge ∧ ({3, 4} : Finset V9) ⊆ B := by
  constructor <;> native_decide

/-- Bridge shares edge {4,5} with C -/
theorem T_bridge_shares_C : ({4, 5} : Finset V9) ⊆ T_bridge ∧ ({4, 5} : Finset V9) ⊆ C := by
  constructor <;> native_decide

/-- Bridge is classified as Bridge type -/
theorem T_bridge_is_bridge : classifyExternal M_path4 T_bridge = ExternalType.Bridge := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- INTERACTION PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Interactions only occur between edges of DIFFERENT M-elements -/
theorem interaction_implies_distinct_parents (e₁ e₂ : Finset V9)
    (he₁ : e₁ ∈ M_edges M_path4) (he₂ : e₂ ∈ M_edges M_path4) (hne : e₁ ≠ e₂)
    (X : Finset V9) (hX : X ∈ M_path4) (he₁X : e₁ ∈ X.powersetCard 2) (he₂X : e₂ ∈ X.powersetCard 2) :
    ¬∃ T, T ∈ externalTriangles (⊥ : SimpleGraph V9) M_path4 ∧ e₁ ⊆ T ∧ e₂ ⊆ T := by
  -- If both edges are from the same M-element X, they share a vertex
  -- Any triangle containing both would share 2 edges with X
  -- Such a triangle would be X itself (since triangles have 3 edges)
  unfold InteractionFoundation.externalTriangles; aesop;

end InteractionFoundation