/-
Tuza ν=4: M_edges_card - Total M-edges = 3 × |M|

GOAL: Prove (M_edges G M).card = 3 * M.card.

SCAFFOLDING (from previous proven slots):
- M_edge_unique_owner (slot155): edges are unique to one M-element
- M_element_has_3_edges (slot156): each M-element has 3 edges

APPROACH:
- M_edges is biUnion of 3-edge sets over M-elements
- Edge sets are pairwise disjoint (by M_edge_unique_owner)
- card_biUnion for disjoint sets = sum of cards = 3 × |M|

1 SORRY: Apply card_biUnion with the disjointness and cardinality facts.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

-- SCAFFOLDING: Proven in slot155
axiom M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) : m1 = m2

-- SCAFFOLDING: Proven in slot156
axiom M_element_has_3_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (m : Finset V) (hm : m ∈ M) :
    (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3

/-- Total M-edges = 3 × |M|. -/
theorem M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card := by
  unfold M_edges
  -- Edge sets from different M-elements are disjoint (by M_edge_unique_owner)
  -- Each has size 3 (by M_element_has_3_edges)
  -- card_biUnion gives sum = 3 × |M|
  -- Key API: Finset.card_biUnion
  sorry
