/-
Tuza ν=4: M_char_optimal - M-characteristic function achieves optimal packingWeight

GOAL: When M.sum(w) = |M|, externals contribute 0, so packingWeight = |M|.

This proves the M-characteristic function (w(m)=1 for m∈M, else 0) is optimal.

SCAFFOLDING:
- external_tradeoff (slot160b): If external t has positive weight, some m ∈ M has w(m) < 1
- packingWeight_split (slot160a): packingWeight = M.sum + externals.sum

APPROACH:
1. If M.sum(w) = |M| and each w(m) ≤ 1, then w(m) = 1 for all m ∈ M
2. By external_tradeoff: any external with positive weight requires some w(m) < 1
3. Since all w(m) = 1, no external can have positive weight
4. Therefore externals.sum(w) = 0
5. packingWeight = M.sum + 0 = |M|

1 SORRY: The deduction that M.sum = |M| and w(m) ≤ 1 implies all w(m) = 1.
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

/-- When M achieves full weight, the M-characteristic function is optimal.

PROOF STRATEGY:
1. M.sum(w) = |M| and each w(m) ≤ 1 implies w(m) = 1 for all m ∈ M
2. By external_tradeoff: positive external weight requires some w(m) < 1
3. Contradiction: if all w(m) = 1, no external can have positive weight
4. Therefore externals.sum(w) = 0
5. packingWeight = M.sum + 0 = |M|
-/
theorem M_char_optimal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w)
    (h_M_weight : M.sum w = M.card)
    (h_bounded : ∀ m ∈ M, w m ≤ 1) :
    packingWeight G w = M.card := by
  rw [packingWeight_split G M hM.1 w hw]
  -- Need: M.sum w + externals.sum w = M.card
  -- We have: M.sum w = M.card
  -- Need to show: externals.sum w = 0
  rw [h_M_weight]
  suffices h : (externals G M).sum w = 0 by linarith
  -- By contradiction: if externals.sum > 0, some external has positive weight
  by_contra h_nonzero
  push_neg at h_nonzero
  -- h_nonzero : externals.sum w ≠ 0
  -- Since w ≥ 0, if sum ≠ 0 then sum > 0 and some element has positive weight
  have h_pos : (externals G M).sum w > 0 := by
    rcases lt_trichotomy ((externals G M).sum w) 0 with h|h|h
    · exfalso
      have : 0 ≤ (externals G M).sum w := Finset.sum_nonneg (fun t _ => hw.1 t)
      linarith
    · exact absurd h h_nonzero
    · exact h
  -- There exists some external with positive weight
  -- (If sum > 0 and all terms ≥ 0, some term must be > 0)
  have h_exists_pos : ∃ t ∈ externals G M, w t > 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    -- h_all_zero : ∀ t ∈ externals, w t ≤ 0
    have : (externals G M).sum w ≤ 0 := Finset.sum_nonpos (fun t ht => h_all_zero t ht)
    linarith
  obtain ⟨t, ht, ht_pos⟩ := h_exists_pos
  -- By external_tradeoff, some m ∈ M has w(m) < 1
  obtain ⟨m, hm, hm_lt⟩ := external_tradeoff G M hM w hw t ht ht_pos
  -- But M.sum = |M| and w ≤ 1 implies all w(m) = 1
  have h_all_one : ∀ m ∈ M, w m = 1 := by
    -- If M.sum = |M| and each w(m) ≤ 1, then each w(m) = 1
    -- (If any w(m) < 1, then M.sum < |M|)
    sorry
  -- Contradiction: w(m) = 1 but w(m) < 1
  have : w m = 1 := h_all_one m hm
  linarith

end
