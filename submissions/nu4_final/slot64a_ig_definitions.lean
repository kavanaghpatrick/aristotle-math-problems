/-
Tuza ν=4 Strategy - Slot 64a: Interaction Graph DEFINITIONS ONLY

This file contains ONLY definitions - no lemmas with sorry.
Aristotle should verify the definitions are well-formed.

DEFINITIONS:
1. M_edges: All edges in packing M
2. externalTriangles: Triangles sharing edge with M but not in M
3. edgesInteract: Two M-edges share an external triangle
4. InteractionGraph: SimpleGraph on M's edges
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ M.card

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n}

-- ══════════════════════════════════════════════════════════════════════════════
-- INTERACTION GRAPH DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- All edges contained in packing elements -/
def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

/-- External triangles: triangles that share edge with M but are not in M -/
def externalTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M ∧ ∃ e ∈ M_edges G M, e ∈ t.sym2)

/-- Triangles sharing a specific edge -/
def trianglesThroughEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)

/-- Two M-edges interact if they both appear in some external triangle.
    KEY: This captures when discarding both edges would miss a triangle. -/
def edgesInteract (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (e₁ e₂ : Sym2 V) : Prop :=
  e₁ ≠ e₂ ∧
  e₁ ∈ M_edges G M ∧
  e₂ ∈ M_edges G M ∧
  ∃ t ∈ externalTriangles G M, e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2

/-- The Interaction Graph on M's edges.
    Vertices: edges in M
    Adjacency: edges interact (share external triangle) -/
def InteractionGraph (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) :
    SimpleGraph (Sym2 V) where
  Adj := edgesInteract G M
  symm := by
    intro e₁ e₂ ⟨hne, he₁, he₂, t, ht, ht₁, ht₂⟩
    exact ⟨hne.symm, he₂, he₁, t, ht, ht₂, ht₁⟩
  loopless := by
    intro e ⟨hne, _, _, _, _, _, _⟩
    exact hne rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- TRIVIAL LEMMAS (should be provable immediately)
-- ══════════════════════════════════════════════════════════════════════════════

/-- External triangles are in G's triangle set -/
lemma external_in_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    t ∈ G.cliqueFinset 3 := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.1

/-- External triangles are not in M -/
lemma external_not_in_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    t ∉ M := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.2.1

/-- External triangles share some edge with M -/
lemma external_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2 := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.2.2

/-- If two edges interact, they share an external triangle witness -/
lemma interact_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : (InteractionGraph G M).Adj e₁ e₂) :
    ∃ t ∈ externalTriangles G M, e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2 := by
  exact h.2.2.2

end
