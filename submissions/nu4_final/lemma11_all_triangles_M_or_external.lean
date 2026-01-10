/-
  lemma11_all_triangles_M_or_external.lean

  LEMMA 11: Every triangle is either an M-element or external to some M-element

  STATEMENT: For any triangle T in G, either T ∈ M or T is external of some A ∈ M

  DIFFICULTY: 4.5/5 (uses maximality of packing)

  PROOF SKETCH:
  - M is a MAXIMAL packing
  - If T ∉ M, then by maximality, T shares an edge with some A ∈ M
  - If T shares edges with multiple M-elements, analyze the structure
  - Key: T can share edge with at most one M-element (else T shares vertex with 2+ M-elements,
    but those M-elements are pairwise edge-disjoint)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter (isTriangle G)

def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t₁ ∧ v ∈ t₁ ∧ u ∈ t₂ ∧ v ∈ t₂

def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isPacking G M ∧
  (∀ T : Finset V, isTriangle G T → T ∉ M → ∃ A ∈ M, sharesEdge T A)

def isExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T A : Finset V) : Prop :=
  isTriangle G T ∧ T ∉ M ∧ A ∈ M ∧ sharesEdge T A ∧
  (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V
  a b c d : V
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup

def Cycle4Config.A (cfg : Cycle4Config V) : Finset V := {cfg.vDA, cfg.vAB, cfg.a}
def Cycle4Config.B (cfg : Cycle4Config V) : Finset V := {cfg.vAB, cfg.vBC, cfg.b}
def Cycle4Config.C (cfg : Cycle4Config V) : Finset V := {cfg.vBC, cfg.vCD, cfg.c}
def Cycle4Config.D (cfg : Cycle4Config V) : Finset V := {cfg.vCD, cfg.vDA, cfg.d}

/-- In cycle_4, triangle T shares edge with at most one M-element -/
theorem shares_edge_with_at_most_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (T : Finset V) (hT : isTriangle G T) (hT_not_M : T ∉ M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (hTA : sharesEdge T A) (hTB : sharesEdge T B) :
    False := by
  -- T shares edge with both A and B (distinct M-elements)
  -- In cycle_4, A and B share at most 1 vertex
  -- T shares 2 vertices with A and 2 with B
  -- So T has at least 3 distinct vertices from A ∪ B
  -- But A and B share at most 1 vertex, so A ∪ B has at least 5 vertices
  -- T can only have 3 vertices... contradiction requires careful analysis
  sorry -- Aristotle: case analysis on which M-elements and shared vertices

/-- LEMMA 11: Every triangle is M-element or external -/
theorem all_triangles_M_or_external
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (T : Finset V) (hT : isTriangle G T) :
    T ∈ M ∨ (∃ A ∈ M, isExternal G M T A) := by
  by_cases hTM : T ∈ M
  · left; exact hTM
  · right
    -- By maximality, T shares edge with some A ∈ M
    obtain ⟨A, hA, hTA⟩ := hM.2 T hT hTM
    use A, hA
    -- Need to show T is external of A (shares edge only with A)
    refine ⟨hT, hTM, hA, hTA, ?_⟩
    intro B hB hBA
    by_contra hTB
    -- T shares edge with both A and B, contradiction
    exact shares_edge_with_at_most_one G M hM.1 hM4 cfg hM_eq T hT hTM A B hA hB hBA hTA hTB

end TuzaNu4
