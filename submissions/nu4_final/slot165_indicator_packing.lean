/-
Tuza ν=4: indicator_is_packing - The indicator 1_M is a valid fractional packing

GOAL: Prove that w(t) = if t ∈ M then 1 else 0 satisfies IsFractionalPacking.

KEY INSIGHT: Each M-edge e appears in exactly ONE M-element (M_edge_unique_owner).
So the edge constraint sum is either:
- 0 (if no M-element contains e) ≤ 1 ✓
- 1 (if exactly one M-element contains e) ≤ 1 ✓

SCAFFOLDING: M_edge_unique_owner (slot155) - PROVEN by Aristotle

1 SORRY: The sum calculation using unique ownership.
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
  have hu1 : u ∈ m1 := he1 u (Or.inl rfl)
  have hv1 : v ∈ m1 := he1 v (Or.inr rfl)
  have hu2 : u ∈ m2 := he2 u (Or.inl rfl)
  have hv2 : v ∈ m2 := he2 v (Or.inr rfl)
  have hu_inter : u ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨hu1, hu2⟩
  have hv_inter : v ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨hv1, hv2⟩
  have h_card : (m1 ∩ m2).card ≥ 2 := Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, hne_uv⟩
  have h_pairwise := hM.2 hm1 hm2 hne
  omega

/-- Helper: M ∩ filter has at most 1 element (unique owner). -/
lemma M_filter_subsingleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) ∩ M).card ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  rw [Finset.one_lt_card] at h_gt
  obtain ⟨m1, hm1, m2, hm2, hne⟩ := h_gt
  rw [Finset.mem_inter, Finset.mem_filter] at hm1 hm2
  have := M_edge_unique_owner G M hM e he m1 m2 hm1.2 hm2.2 hm1.1.2 hm2.1.2
  exact hne this

/-- The indicator function 1_M is a valid fractional packing. -/
theorem indicator_is_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    IsFractionalPacking G (fun t => if t ∈ M then 1 else 0) := by
  let w : Finset V → ℝ := fun t => if t ∈ M then 1 else 0
  constructor
  -- Nonnegativity
  · intro t; simp only [w]; split_ifs <;> linarith
  constructor
  -- Zero outside triangles
  · intro t ht; simp only [w]
    split_ifs with h
    · exact absurd (hM.1 h) ht
    · rfl
  -- Edge constraints: for each e, sum ≤ 1
  · intro e he
    -- Split sum into M and non-M parts
    have h_M_triangle : M ⊆ G.cliqueFinset 3 := hM.1
    let S := (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)
    have h_partition : S = (S ∩ M) ∪ (S \ M) := by
      ext t; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, S]
      constructor
      · intro ht; by_cases hM' : t ∈ M <;> [left; right] <;> exact ⟨ht, hM'⟩
      · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht
    have h_disj : Disjoint (S ∩ M) (S \ M) := Finset.disjoint_sdiff
    calc S.sum w = (S ∩ M).sum w + (S \ M).sum w := by
           rw [h_partition, Finset.sum_union h_disj]
      _ = (S ∩ M).sum (fun _ => (1 : ℝ)) + (S \ M).sum (fun _ => (0 : ℝ)) := by
           congr 1
           · apply Finset.sum_congr rfl
             intro t ht; rw [Finset.mem_inter] at ht
             simp only [w, if_pos ht.2]
           · apply Finset.sum_congr rfl
             intro t ht; rw [Finset.mem_sdiff] at ht
             simp only [w, if_neg ht.2]
      _ = (S ∩ M).card + 0 := by simp
      _ = (S ∩ M).card := by ring
      _ ≤ 1 := by
           -- By M_filter_subsingleton, |S ∩ M| ≤ 1
           have h_sub := M_filter_subsingleton G M hM e he
           simp only [S] at h_sub
           -- Need Nat to Real conversion
           sorry  -- Aristotle: (S ∩ M).card ≤ 1 implies (↑(S ∩ M).card : ℝ) ≤ 1

end
