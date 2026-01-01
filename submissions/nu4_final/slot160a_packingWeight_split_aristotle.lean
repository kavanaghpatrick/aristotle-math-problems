/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d327a427-b237-4132-8c05-36475e644f96

The following was proved by Aristotle:

- theorem packingWeight_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w = M.sum w + (externals G M).sum w
-/

/-
Tuza ν=4: packingWeight_split - packingWeight = M.sum + externals.sum

GOAL: Prove that packingWeight splits into M-contribution and external-contribution.

This is a simple set-theoretic identity: cliqueFinset 3 = M ∪ externals (disjoint).

1 SORRY: The disjoint union identity for sums.
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  (G.cliqueFinset 3).sum w

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M)

/-- packingWeight splits into M-sum and externals-sum.

PROOF STRATEGY:
1. M ⊆ cliqueFinset 3 (from isTrianglePacking)
2. externals = cliqueFinset 3 \ M (by definition, but using filter)
3. cliqueFinset 3 = M ∪ externals (disjoint union)
4. sum over cliqueFinset 3 = sum over M + sum over externals
-/
theorem packingWeight_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w = M.sum w + (externals G M).sum w := by
  unfold packingWeight externals
  -- Need to show: (cliqueFinset 3).sum w = M.sum w + (filter (∉ M) (cliqueFinset 3)).sum w
  -- This follows from sum_union when M and externals partition cliqueFinset 3
  -- Since M ⊆ cliqueFinset 3 and externals = cliqueFinset 3 \ M
  rw [ ← Finset.sum_union ];
  · congr with t ; by_cases ht : t ∈ M <;> simp +decide [ ht ];
    have := hM.1 ht; aesop;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_filter.mp hx₂ |>.2 hx₁