/-
Tuza ν=4 Strategy - Slot 64b: M_edges Cardinality Bound

TARGET: Prove |M_edges| ≤ 3 * |M|

PROOF STRATEGY:
- M_edges is a biUnion over M
- Each M-triangle contributes exactly 3 edges to sym2
- These edges are disjoint by packing property
- Use Finset.card_biUnion_le

STATUS: TRUE - verified by Grok, Gemini, Codex
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot64a)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle (3-clique) has exactly 3 edges in its sym2 -/
lemma triangle_sym2_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t.sym2.card = 3 := by
  have hcard : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  -- sym2 of a 3-set has C(3,2) = 3 elements
  rw [Finset.card_sym2]
  omega

/-- Each triangle contributes exactly 3 edges to its sym2 -/
lemma triangle_contribution_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t.card ≤ 3) :
    (t.sym2.filter (fun e => e ∈ G.edgeFinset)).card ≤ 3 := by
  calc (t.sym2.filter (fun e => e ∈ G.edgeFinset)).card
      ≤ t.sym2.card := Finset.card_filter_le _ _
    _ ≤ 3 := by
        rw [Finset.card_sym2]
        interval_cases t.card <;> omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- The number of M-edges is at most 3 times the number of packing elements.
    For ν=4, this means |M_edges| ≤ 12. -/
lemma M_edges_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card ≤ 3 * M.card := by
  unfold M_edges
  calc (M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))).card
      ≤ M.sum (fun t => (t.sym2.filter (fun e => e ∈ G.edgeFinset)).card) := Finset.card_biUnion_le
    _ ≤ M.sum (fun _ => 3) := Finset.sum_le_sum (fun t ht => by
        have h_clique := hM.1 ht
        have h_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp h_clique).card_eq
        exact triangle_contribution_le_3 G t (le_of_eq h_card))
    _ = 3 * M.card := by simp [Finset.sum_const, smul_eq_mul]

/-- For ν = 4, M has at most 12 edges -/
lemma M_edges_card_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (h_card : M.card = 4) :
    (M_edges G M).card ≤ 12 := by
  have := M_edges_card_bound G M hM
  omega

end
