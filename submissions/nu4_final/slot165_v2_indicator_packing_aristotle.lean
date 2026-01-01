/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c059b320-4202-41ac-8f45-bf7ba56ff402
-/

/-
Tuza ν=4: indicator_is_packing - The indicator 1_M is a valid fractional packing

GOAL: Prove that w(t) = if t ∈ M then 1 else 0 satisfies IsFractionalPacking.

KEY INSIGHT: Each M-edge e appears in exactly ONE M-element (M_edge_unique_owner).
So the edge constraint sum is at most 1.

FIX from v1: Corrected disjoint lemma and Nat/Real cast.

1 SORRY: The final card ≤ 1 arithmetic step.
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset,
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

-- PROVEN in slot155 by Aristotle
lemma M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he_edge : e ∈ G.edgeFinset)
    (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2 := by
  by_contra hne
  rw [SimpleGraph.mem_edgeFinset] at he_edge
  obtain ⟨u, v⟩ := e
  have hne_uv : u ≠ v := G.ne_of_adj he_edge
  simp only [Finset.mem_sym2_iff, Sym2.mem_iff] at he1 he2
  have hu_inter : u ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨he1 u (Or.inl rfl), he2 u (Or.inl rfl)⟩
  have hv_inter : v ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨he1 v (Or.inr rfl), he2 v (Or.inr rfl)⟩
  have h_card : (m1 ∩ m2).card ≥ 2 := Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, hne_uv⟩
  exact Nat.lt_irrefl 1 (Nat.lt_of_lt_of_le (hM.2 hm1 hm2 hne) h_card)

/-- Helper: At most one M-element contains edge e. -/
lemma M_filter_card_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) ∩ M).card ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  obtain ⟨m1, hm1, m2, hm2, hne⟩ := Finset.one_lt_card.mp h_gt
  simp only [Finset.mem_inter, Finset.mem_filter] at hm1 hm2
  exact hne (M_edge_unique_owner G M hM e he m1 m2 hm1.2 hm2.2 hm1.1.2 hm2.1.2)

/-- The indicator function 1_M is a valid fractional packing. -/
theorem indicator_is_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    IsFractionalPacking G (fun t => if t ∈ M then 1 else 0) := by
  let w : Finset V → ℝ := fun t => if t ∈ M then 1 else 0
  refine ⟨fun t => by simp only [w]; split_ifs <;> linarith,
          fun t ht => by simp only [w]; split_ifs with h; exact absurd (hM.1 h) ht; rfl, ?_⟩
  intro e he
  let S := (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)
  -- Sum over S = sum over (S ∩ M) + sum over (S \ M)
  have h_sum_split : S.sum w = (S ∩ M).sum w + (S \ M).sum w := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter.symm)]
    congr 1
    ext t; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro ht; by_cases h : t ∈ M <;> [right; left] <;> exact ⟨ht, h⟩
    · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht
  -- On S ∩ M: w = 1 (constant), so sum = card
  have h_M_sum : (S ∩ M).sum w = (S ∩ M).card := by
    rw [Finset.sum_eq_card_nsmul (s := S ∩ M) (b := 1)]
    · simp
    · intro t ht
      simp only [Finset.mem_inter] at ht
      simp only [w, if_pos ht.2]
  -- On S \ M: w = 0, so sum = 0
  have h_nonM_sum : (S \ M).sum w = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_sdiff] at ht
    simp only [w, if_neg ht.2]
  -- |S ∩ M| ≤ 1 by M_filter_card_le_one
  have h_card_le : (S ∩ M).card ≤ 1 := M_filter_card_le_one G M hM e he
  -- Combine: S.sum w = |S ∩ M| + 0 ≤ 1
  calc S.sum w = (S ∩ M).sum w + (S \ M).sum w := h_sum_split
    _ = (S ∩ M).card + 0 := by rw [h_M_sum, h_nonM_sum]
    _ = (S ∩ M).card := by ring
    _ ≤ 1 := by
        -- Nat ≤ 1 implies Real ≤ 1
        have h_real : ((S ∩ M).card : ℝ) ≤ (1 : ℕ) := Nat.cast_le.mpr h_card_le
        simp at h_real
        exact h_real

end