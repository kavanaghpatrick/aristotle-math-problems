/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0d36f3d8-8662-4df5-97f6-0f6f1b36b6fd
-/

/-
Tuza ν=4 Strategy - Slot 65: Singleton & Conflict Definitions

TARGET: Define predicates for "dangerous" edges to discard

DEFINITIONS:
1. SingletonEdge: An M-edge e is a singleton if some external triangle T
   has T ∩ M_edges = {e} (only one M-edge in T)
2. ConflictPair: Two M-edges conflict if some external triangle T
   has T ∩ M_edges = {e₁, e₂} (exactly these two M-edges)

SIGNIFICANCE:
- Discarding a SingletonEdge would leave T uncovered
- Discarding both of a ConflictPair would leave T uncovered
- Safe discard set must avoid singletons and not contain both of any conflict pair

STATUS: DEFINITIONS ONLY - Aristotle should verify well-formedness
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING (from slot64a)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

def externalTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M ∧ ∃ e ∈ M_edges G M, e ∈ t.sym2)

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW DEFINITIONS: Singleton Edges and Conflict Pairs
-- ══════════════════════════════════════════════════════════════════════════════

/-- The M-edges contained in a triangle -/
def M_edges_in (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (t : Finset V) : Finset (Sym2 V) :=
  (M_edges G M).filter (fun e => e ∈ t.sym2)

/-- An edge is a "singleton" if some external triangle contains ONLY this M-edge.
    Discarding a singleton would leave that triangle uncovered. -/
def SingletonEdge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (e : Sym2 V) : Prop :=
  e ∈ M_edges G M ∧
  ∃ t ∈ externalTriangles G M, M_edges_in G M t = {e}

/-- Two edges form a "conflict pair" if some external triangle contains exactly these two.
    Discarding both would leave that triangle uncovered. -/
def ConflictPair (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (e₁ e₂ : Sym2 V) : Prop :=
  e₁ ∈ M_edges G M ∧
  e₂ ∈ M_edges G M ∧
  e₁ ≠ e₂ ∧
  ∃ t ∈ externalTriangles G M, M_edges_in G M t = {e₁, e₂}

/-- A set of edges is "safe to discard" if:
    1. It contains no singletons
    2. For every conflict pair, it contains at most one edge -/
def SafeDiscardSet (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (D : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ D, ¬SingletonEdge G M e) ∧
  (∀ e₁ e₂, ConflictPair G M e₁ e₂ → ¬(e₁ ∈ D ∧ e₂ ∈ D))

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- External triangles contain at least one M-edge (by definition) -/
lemma external_has_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    (M_edges_in G M t).Nonempty := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  obtain ⟨_, _, e, he_M, he_t⟩ := ht
  exact ⟨e, Finset.mem_filter.mpr ⟨he_M, he_t⟩⟩

/-- External triangles contain at most 3 M-edges (since triangles have 3 edges total) -/
lemma external_M_edges_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (M_edges_in G M t).card ≤ 3 := by
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  calc (M_edges_in G M t).card
      ≤ t.sym2.card := Finset.card_filter_le _ _
    _ = 3 := by rw [Finset.card_sym2]; omega

/-- Conflict pairs can only occur between edges that share a vertex -/
lemma conflict_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : ConflictPair G M e₁ e₂) :
    ∃ v, v ∈ e₁.toFinset ∧ v ∈ e₂.toFinset := by
  obtain ⟨_, _, hne, t, ht, heq⟩ := h
  simp only [externalTriangles, Finset.mem_filter] at ht
  have ht_clique := ht.1
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht_clique).card_eq
  -- e₁ and e₂ are both in t.sym2
  have he₁_t : e₁ ∈ t.sym2 := by
    have : e₁ ∈ M_edges_in G M t := by rw [heq]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_filter.mp this).2
  have he₂_t : e₂ ∈ t.sym2 := by
    have : e₂ ∈ M_edges_in G M t := by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_filter.mp this).2
  -- Two edges in a 3-set share a vertex
  rw [Finset.mem_sym2_iff] at he₁_t he₂_t
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := he₁_t
  obtain ⟨c, d, hcd, hc, hd, rfl⟩ := he₂_t
  -- If {a,b} ∩ {c,d} = ∅, then |{a,b,c,d}| = 4 > 3 = |t|
  by_cases h1 : a = c
  · exact ⟨a, by simp, by simp [h1]⟩
  by_cases h2 : a = d
  · exact ⟨a, by simp, by simp [h2]⟩
  by_cases h3 : b = c
  · exact ⟨b, by simp, by simp [h3]⟩
  by_cases h4 : b = d
  · exact ⟨b, by simp, by simp [h4]⟩
  -- All four distinct → contradiction
  have h_four : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h4, h3]
    · simp [h2, h1]
    · simp [hab]
  have h_sub : ({a, b, c, d} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

end