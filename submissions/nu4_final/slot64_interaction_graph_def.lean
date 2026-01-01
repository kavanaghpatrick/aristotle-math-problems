/-
Tuza ν=4 Strategy - Slot 64: Interaction Graph Definition

NEW APPROACH: Safe Discard + Interaction Graph
This is the foundation for the direct combinatorial proof (NOT using Krivelevich LP).

INTERACTION GRAPH (IG):
- Vertices: The 12 edges of M (4 triangles × 3 edges each)
- Adjacency: Two M-edges are adjacent iff they both appear in some EXTERNAL triangle
- An EXTERNAL triangle is one that shares edge with M but is NOT in M

KEY INSIGHT:
If we find a 4-edge independent set in IG (one edge per M-triangle),
we can "safely discard" those 4 edges and cover with the remaining 8.

This file establishes:
1. Definition of M_edges (all edges in packing)
2. Definition of external triangles
3. Definition of InteractionGraph
4. Basic properties

SCAFFOLDING: Uses proven lemmas from slot63 (UUID: 3d31b863)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS (from slot63 scaffolding)
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
-- NEW DEFINITIONS: M_edges and External Triangles
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

-- ══════════════════════════════════════════════════════════════════════════════
-- INTERACTION GRAPH DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two M-edges interact if they both appear in some external triangle.
    This is the KEY definition for the Safe Discard approach. -/
def edgesInteract (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (e₁ e₂ : Sym2 V) : Prop :=
  e₁ ≠ e₂ ∧
  e₁ ∈ M_edges G M ∧
  e₂ ∈ M_edges G M ∧
  ∃ t ∈ externalTriangles G M, e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2

/-- The Interaction Graph on M's edges -/
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
-- BASIC PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- M_edges contains exactly 3 edges per triangle in packing -/
lemma M_edges_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card ≤ 3 * M.card := by
  sorry -- Each triangle contributes at most 3 edges

/-- For ν = 4, M has at most 12 edges -/
lemma M_edges_card_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (h_card : M.card = 4) :
    (M_edges G M).card ≤ 12 := by
  have := M_edges_card_bound G M hM
  omega

/-- External triangles share at least one edge with M (by definition) -/
lemma external_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2 := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.2.2

/-- External triangles are not in M -/
lemma external_not_in_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    t ∉ M := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.2.1

/-- If two edges interact, they share an external triangle -/
lemma interact_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : (InteractionGraph G M).Adj e₁ e₂) :
    ∃ t ∈ externalTriangles G M, e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2 := by
  exact h.2.2.2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot63)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each edge in a triangle packing appears in exactly one triangle. -/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  rw [Finset.mem_sym2_iff] at he he'
  obtain ⟨u, v, huv, hu_m, hv_m, rfl⟩ := he
  obtain ⟨u', v', _, hu'_m', hv'_m', heq⟩ := he'
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hu'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hv'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hv'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hu'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega

/-- Every triangle shares ≥2 vertices with some M-element (maximality). -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  obtain ⟨hM_triangle_packing, hM_max⟩ := hM
  contrapose! hM_max
  refine ⟨insert t M, ?_, ?_⟩
  · simp only [isTrianglePacking, Finset.subset_iff, Set.Pairwise] at *
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM_triangle_packing.1 hx
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact Nat.le_of_lt_succ (hM_max y hy)
      · rw [Finset.inter_comm]; exact Nat.le_of_lt_succ (hM_max x hx)
      · exact hM_triangle_packing.2 hx hy hxy
  · rw [Finset.card_insert_of_not_mem]
    · omega
    · intro ht_in_M
      specialize hM_max t ht_in_M
      have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
      omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: External triangles share edge with exactly one M-element
-- ══════════════════════════════════════════════════════════════════════════════

/-- An external triangle shares edge with exactly one M-element.
    (If it shared edge with two, it would violate packing disjointness) -/
lemma external_shares_unique_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∈ externalTriangles G M) :
    ∃! m, m ∈ M ∧ ∃ e ∈ t.sym2, e ∈ m.sym2 := by
  sorry -- Use M_edge_in_exactly_one

-- ══════════════════════════════════════════════════════════════════════════════
-- DEGREE BOUND (for Turán-style arguments)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each M-edge has bounded degree in the Interaction Graph.
    This enables finding independent sets. -/
lemma ig_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ M_edges G M) :
    (InteractionGraph G M).degree e ≤ 6 := by
  sorry -- Each edge can interact with at most 2 edges per other M-triangle

end
