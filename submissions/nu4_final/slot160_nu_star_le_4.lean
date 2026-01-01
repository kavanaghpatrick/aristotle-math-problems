/-
Tuza ν=4: nu_star_le_4 - Any fractional packing has weight ≤ 4

GOAL: Prove packingWeight G w ≤ 4 when |M| = 4.

SCAFFOLDING (from previous proven slots):
- M_weight_le_card (slot159): M.sum w ≤ |M|
- external_shares_M_edge (slot158): externals share M-edges
- M_edge_unique_owner (slot155): M-edges are unique to one element

APPROACH (LP Optimality):
1. packingWeight = M.sum w + externals.sum w
2. By slot159: M.sum w ≤ |M| = 4
3. Key insight: Each external shares an M-edge (slot158)
4. Each M-edge has constraint: sum of weights ≤ 1
5. M-char saturates M-edges, so externals must trade-off with M
6. Total weight ≤ 4

1 SORRY: The LP optimality / complementary slackness argument.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- DEFINITIONS

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  (G.cliqueFinset 3).sum w

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M)

-- SCAFFOLDING: Proven in slot155
axiom M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) : m1 = m2

-- SCAFFOLDING: Proven in slot158
axiom external_shares_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ externals G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2

-- SCAFFOLDING: Proven in slot159
axiom M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card

/-- Any fractional packing has weight at most 4 when |M| = 4.

PROOF STRATEGY (LP Complementary Slackness):
1. packingWeight = (cliqueFinset 3).sum w = M.sum w + externals.sum w
2. Each external t shares M-edge e with some m ∈ M (by external_shares_M_edge)
3. Edge constraint: w(m) + w(t) + ... ≤ 1
4. Summing carefully over M-edges with double-counting analysis:
   - Each M-element m has 3 M-edges, contributing 3×w(m)
   - Each external uses ≥1 M-edge, contributing ≥1×w(ext)
5. Sum of M-edge constraints: 3×M.sum(w) + externals.sum(w) ≤ 3|M|
6. Combined with M ⊆ cliqueFinset 3: packingWeight ≤ 4

Key insight: The edge constraint coupling between M-elements and externals
limits total weight to 4 = |M|.
-/
theorem nu_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ 4 := by
  -- The LP optimality argument:
  -- 1. Each M-element has 3 edges, each external has ≥1 M-edge
  -- 2. Summing constraints: 3×M.sum(w) + ≥1×externals.sum(w) ≤ 3|M| = 12
  -- 3. packingWeight = M.sum(w) + externals.sum(w)
  -- 4. From (2): externals.sum(w) ≤ 12 - 3×M.sum(w)
  -- 5. packingWeight = M.sum(w) + externals.sum(w) ≤ M.sum(w) + 12 - 3×M.sum(w) = 12 - 2×M.sum(w)
  -- 6. Since w ≥ 0: M.sum(w) ≥ 0, so packingWeight ≤ 12
  -- 7. But we need ≤ 4! Tighter analysis via LP duality:
  --    The M-characteristic function achieves packingWeight = 4 and is optimal.
  --    Any other w satisfying constraints also achieves ≤ 4.
  sorry

end
