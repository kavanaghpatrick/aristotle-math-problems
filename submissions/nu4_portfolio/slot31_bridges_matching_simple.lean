/-
Tuza ν=4 - Bridges Form Matching (Simplified)

TARGET: bridges_inter_card_eq_one - Two distinct bridges share exactly one vertex

KEY INSIGHT:
If t1, t2 are both bridges (share edges with two packing elements each),
then |t1 ∩ t2| = 1.

Why: Each bridge shares edges with exactly 2 packing elements.
If t1, t2 shared 2+ vertices, they'd share an edge, contradicting
that packing elements are edge-disjoint.

This is the foundation for the "bridges form a matching" argument
needed for the star case of ν=4.

SCAFFOLDING: Te_eq_Se_union_bridges, tau_S_le_2 (proven in slot6)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (minimal set)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  M.biUnion (bridges G M)

-- A bridge is a triangle that shares an edge with at least 2 packing elements
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ (M.filter (fun e => (t ∩ e).card ≥ 2)).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- Two triangles sharing 2+ vertices share an edge
lemma triangles_sharing_two_vertices_share_edge (t1 t2 : Finset V)
    (ht1 : t1.card = 3) (ht2 : t2.card = 3) (h : (t1 ∩ t2).card ≥ 2) :
    ∃ u v, u ≠ v ∧ u ∈ t1 ∧ v ∈ t1 ∧ u ∈ t2 ∧ v ∈ t2 := by
  sorry

-- Packing elements are edge-disjoint (share at most 1 vertex)
lemma packing_edge_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (e ∩ f).card ≤ 1 := by
  exact hM.2 he hf hef

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge shares edge with at most one packing element's edge
-- ══════════════════════════════════════════════════════════════════════════════

-- If a bridge shares edges with e and f, then e and f must share a vertex
lemma bridge_implies_packing_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (ht_tri : t ∈ G.cliqueFinset 3)
    (ht_e : (t ∩ e).card ≥ 2) (ht_f : (t ∩ f).card ≥ 2) :
    (e ∩ f).card = 1 := by
  -- t shares ≥2 vertices with e, so shares an edge with e
  -- t shares ≥2 vertices with f, so shares an edge with f
  -- t has only 3 vertices, e has 3, f has 3
  -- If e ∩ f = ∅, then t would need ≥4 vertices to share 2 with each
  -- So e ∩ f ≠ ∅, meaning |e ∩ f| ≥ 1
  -- But |e ∩ f| ≤ 1 by packing property
  sorry

-- The shared vertex is in the bridge
lemma bridge_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (ht_tri : t ∈ G.cliqueFinset 3)
    (ht_e : (t ∩ e).card ≥ 2) (ht_f : (t ∩ f).card ≥ 2)
    (v : V) (hv : e ∩ f = {v}) :
    v ∈ t := by
  -- t shares edge with e: has 2 vertices from e
  -- t shares edge with f: has 2 vertices from f
  -- e ∩ f = {v}, so v is the only common vertex
  -- For t to share 2 with e and 2 with f, it must include v
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN TARGET: Two bridges share exactly one vertex
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridges_inter_card_eq_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ allBridges G M) (ht2 : t2 ∈ allBridges G M) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card = 1 := by
  -- t1 is a bridge: shares edges with some e1, f1 ∈ M (e1 ≠ f1)
  -- t2 is a bridge: shares edges with some e2, f2 ∈ M (e2 ≠ f2)
  -- By bridge_implies_packing_share_vertex: e1 ∩ f1 = {v1}, e2 ∩ f2 = {v2}
  -- By bridge_contains_shared_vertex: v1 ∈ t1, v2 ∈ t2
  --
  -- Case 1: {e1, f1} = {e2, f2} (same pair of packing elements)
  --   Then v1 = v2, and both t1, t2 contain v
  --   If |t1 ∩ t2| ≥ 2, they share an edge
  --   But both share edges with e1 and f1, which are edge-disjoint
  --   This forces |t1 ∩ t2| = 1
  --
  -- Case 2: {e1, f1} ≠ {e2, f2}
  --   Similar analysis using that packing is edge-disjoint
  sorry

-- Corollary: Bridges are pairwise "nearly disjoint" (share only the hub in star case)
theorem bridges_pairwise_share_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (h_star : ∀ e ∈ M, v ∈ e) :
    ∀ t1 ∈ allBridges G M, ∀ t2 ∈ allBridges G M, t1 ≠ t2 →
      t1 ∩ t2 = {v} := by
  -- In star case, all packing elements share v
  -- By bridges_inter_card_eq_one: |t1 ∩ t2| = 1
  -- The shared vertex must be v (since bridges go through shared vertices of packing)
  sorry

end
