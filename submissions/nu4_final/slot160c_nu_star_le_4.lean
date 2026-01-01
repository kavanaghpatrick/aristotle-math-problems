/-
Tuza ν=4: nu_star_le_4 - Any fractional packing has weight ≤ 4

GOAL: Prove packingWeight G w ≤ 4 when |M| = 4.

SCAFFOLDING:
- packingWeight_split (slot160a): packingWeight = M.sum + externals.sum
- external_tradeoff (slot160b): externals trade off with M-elements
- M_weight_le_card (slot159): M.sum w ≤ |M|

APPROACH (Trade-off Analysis):
1. packingWeight = M.sum(w) + externals.sum(w)
2. When M.sum(w) = |M| = 4, M-char saturates all M-edges
3. Each external shares an M-edge (slot158) with a saturated constraint
4. Therefore externals.sum(w) = 0 when M.sum(w) = |M|
5. If M.sum(w) < |M|, the slack goes to externals but trade-off is 1:1
6. Maximum packingWeight = 4

1 SORRY: The final trade-off analysis.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

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

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M)

-- SCAFFOLDING: Proven in slot159
axiom M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card

-- SCAFFOLDING: Proven in slot160a
axiom packingWeight_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w = M.sum w + (externals G M).sum w

-- SCAFFOLDING: Proven in slot160b
axiom external_tradeoff (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w)
    (t : Finset V) (ht : t ∈ externals G M) (h_pos : w t > 0) :
    ∃ m ∈ M, w m < 1

/-- Any fractional packing has weight at most 4 when |M| = 4.

PROOF STRATEGY:
1. packingWeight = M.sum(w) + externals.sum(w) (by packingWeight_split)
2. By M_weight_le_card: M.sum(w) ≤ 4
3. The key: externals.sum(w) ≤ 4 - M.sum(w)

The trade-off argument:
- Consider the M-characteristic function M_char (w(m)=1 for m∈M, else 0)
- M_char achieves packingWeight = 4 and saturates all M-edges
- For any other w, if some m has w(m) < 1, there's "slack" at m's edges
- An external can use that slack, but the trade is at most 1:1
- Therefore packingWeight ≤ 4
-/
theorem nu_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ 4 := by
  rw [packingWeight_split G M hM.1 w hw]
  -- Need: M.sum w + externals.sum w ≤ 4
  -- We have: M.sum w ≤ 4 (from M_weight_le_card)
  -- Key insight: The trade-off between M and externals is at most 1:1
  --
  -- Let deficit = 4 - M.sum(w) ≥ 0 (by M_weight_le_card)
  -- Claim: externals.sum(w) ≤ deficit
  --
  -- Proof sketch:
  -- - Each external t with w(t) > 0 requires some m with w(m) < 1 (external_tradeoff)
  -- - The "slack" at m's edges (1 - w(m)) can support at most that much external weight
  -- - Summing over all M-elements: total slack = 4 - M.sum(w) = deficit
  -- - Therefore externals.sum(w) ≤ deficit
  sorry

end
