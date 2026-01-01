/-
Tuza ν=4: MAIN THEOREM - ν* = 4

GOAL: Prove ν* = 4 for maximal packing M with |M| = 4.

FIX: The packingWeight = 4 proof needed explicit simp on sums.

PROVEN SCAFFOLDING (all from previous Aristotle runs):
- M_edge_unique_owner, M_weight_le_card, externals_zero_when_saturated
- indicator_is_packing (slot165_v2)

1 SORRY: The exchange argument for packingWeight ≤ 4
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

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  (G.cliqueFinset 3).sum w

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3) \ M

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

-- ═══════════════════════════════════════════════════════════════════════
-- SCAFFOLDING (PROVEN by Aristotle)
-- ═══════════════════════════════════════════════════════════════════════

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

lemma M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card := by
  have h_each_le_1 : ∀ m ∈ M, w m ≤ 1 := by
    intro m hm
    have h_clique := hM.1 hm
    have h_is_clique := SimpleGraph.mem_cliqueFinset_iff.mp h_clique
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.card_le_two.not.mp (by omega : ¬m.card ≤ 2)
    have h_adj : G.Adj a b := h_is_clique.2 ha hb hab
    let e := Sym2.mk (a, b)
    have h_e_edge : e ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr h_adj
    have h_e_in_m : e ∈ m.sym2 := by
      rw [Finset.mem_sym2_iff]; intro x hx
      simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> assumption
    have h_m_in : m ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) :=
      Finset.mem_filter.mpr ⟨h_clique, h_e_in_m⟩
    calc w m ≤ ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w :=
           Finset.single_le_sum (fun t _ => hw.1 t) h_m_in
      _ ≤ 1 := hw.2.2 e h_e_edge
  calc M.sum w ≤ M.sum (fun _ => (1 : ℝ)) := Finset.sum_le_sum (fun m hm => h_each_le_1 m hm)
    _ = M.card := by simp

lemma external_shares_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ externals G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2 := by
  rw [externals, Finset.mem_sdiff] at ht
  obtain ⟨ht_clique, ht_not_M⟩ := ht
  obtain ⟨m, hm, h_inter⟩ := hM.2 t ht_clique ht_not_M
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.card_le_two.not.mp (by omega : ¬(t ∩ m).card ≤ 2)
  rw [Finset.mem_inter] at ha hb
  let e := Sym2.mk (a, b)
  have h_e_in_t : e ∈ t.sym2 := by
    rw [Finset.mem_sym2_iff]; intro x hx
    simp only [Sym2.mem_iff, e] at hx; rcases hx with rfl | rfl <;> [exact ha.1; exact hb.1]
  have h_e_in_m : e ∈ m.sym2 := by
    rw [Finset.mem_sym2_iff]; intro x hx
    simp only [Sym2.mem_iff, e] at hx; rcases hx with rfl | rfl <;> [exact ha.2; exact hb.2]
  have h_adj : G.Adj a b := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hm)).2 ha.2 hb.2 hab
  have h_e_edge : e ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr h_adj
  exact ⟨e, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_filter.mpr ⟨h_e_in_m, h_e_edge⟩⟩, h_e_in_t⟩

theorem externals_zero_when_saturated (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w)
    (h_sat : ∀ m ∈ M, w m = 1) :
    ∀ t ∈ externals G M, w t = 0 := by
  intro t ht
  obtain ⟨e, he_M, he_t⟩ := external_shares_M_edge G M hM t ht
  rw [M_edges, Finset.mem_biUnion] at he_M
  obtain ⟨m, hm, he_m_filter⟩ := he_M
  obtain ⟨he_m, he_edge⟩ := Finset.mem_filter.mp he_m_filter
  have h_constr := hw.2.2 e he_edge
  have ht_clique : t ∈ G.cliqueFinset 3 := (Finset.mem_sdiff.mp ht).1
  have h_t_ne_m : t ≠ m := fun h => (Finset.mem_sdiff.mp ht).2 (h ▸ hm)
  have h_m_in : m ∈ (G.cliqueFinset 3).filter (fun s => e ∈ s.sym2) :=
    Finset.mem_filter.mpr ⟨hM.1.1 hm, he_m⟩
  have h_t_in : t ∈ (G.cliqueFinset 3).filter (fun s => e ∈ s.sym2) :=
    Finset.mem_filter.mpr ⟨ht_clique, he_t⟩
  have h_sum_ge : w m + w t ≤ ((G.cliqueFinset 3).filter (fun s => e ∈ s.sym2)).sum w := by
    have h_sub : ({m, t} : Finset (Finset V)) ⊆ (G.cliqueFinset 3).filter (fun s => e ∈ s.sym2) := by
      intro s hs; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> assumption
    calc w m + w t = ({m, t} : Finset (Finset V)).sum w := (Finset.sum_pair h_t_ne_m.symm).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset (fun s hs => h_sub hs) (fun s _ _ => hw.1 s)
  rw [h_sat m hm] at h_sum_ge
  linarith [hw.1 t]

lemma M_filter_card_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) ∩ M).card ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  obtain ⟨m1, hm1, m2, hm2, hne⟩ := Finset.one_lt_card.mp h_gt
  simp only [Finset.mem_inter, Finset.mem_filter] at hm1 hm2
  exact hne (M_edge_unique_owner G M hM e he m1 m2 hm1.2 hm2.2 hm1.1.2 hm2.1.2)

theorem indicator_is_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    IsFractionalPacking G (fun t => if t ∈ M then 1 else 0) := by
  let w : Finset V → ℝ := fun t => if t ∈ M then 1 else 0
  refine ⟨fun t => by simp only [w]; split_ifs <;> linarith,
          fun t ht => by simp only [w]; split_ifs with h; exact absurd (hM.1 h) ht; rfl, ?_⟩
  intro e he
  let S := (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)
  have h_sum : S.sum w = (S ∩ M).card := by
    rw [← Finset.sum_inter_add_sum_diff S M w]
    have h1 : (S ∩ M).sum w = (S ∩ M).card := by
      simp only [w]; rw [Finset.sum_ite_mem, Finset.inter_comm M (S ∩ M)]
      simp [Finset.inter_assoc]
    have h2 : (S \ M).sum w = 0 := by
      apply Finset.sum_eq_zero; intro t ht
      simp only [Finset.mem_sdiff] at ht; simp only [w, if_neg ht.2]
    linarith
  calc S.sum w = (S ∩ M).card := h_sum
    _ ≤ 1 := M_filter_card_le_one G M hM e he

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════════════

theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    ∃ w, IsFractionalPacking G w ∧ packingWeight G w = 4 ∧
         ∀ w', IsFractionalPacking G w' → packingWeight G w' ≤ 4 := by
  let w₀ : Finset V → ℝ := fun t => if t ∈ M then 1 else 0
  use w₀
  refine ⟨indicator_is_packing G M hM.1, ?_, ?_⟩
  -- packingWeight w₀ = 4
  · unfold packingWeight
    have h_part : G.cliqueFinset 3 = M ∪ externals G M := by
      ext t; simp only [Finset.mem_union, externals, Finset.mem_sdiff]
      constructor
      · intro ht; by_cases h : t ∈ M <;> [left; right] <;> [exact h; exact ⟨ht, h⟩]
      · intro h; rcases h with h | ⟨h, _⟩ <;> [exact hM.1.1 h; exact h]
    have h_disj : Disjoint M (externals G M) := by
      rw [Finset.disjoint_left]; intro t ht hext
      exact (Finset.mem_sdiff.mp hext).2 ht
    rw [h_part, Finset.sum_union h_disj]
    -- Explicit computation of M.sum w₀
    have hM_sum : M.sum w₀ = (M.card : ℝ) := by
      trans M.sum (fun _ => (1 : ℝ))
      · apply Finset.sum_congr rfl
        intro t ht
        simp only [w₀, if_pos ht]
      · simp
    -- Externals sum to 0
    have hext_sum : (externals G M).sum w₀ = 0 := by
      apply Finset.sum_eq_zero; intro t ht
      simp only [w₀, externals, Finset.mem_sdiff] at ht ⊢
      simp only [if_neg ht.2]
    rw [hM_sum, hext_sum, hM4]
    ring
  -- All packings have weight ≤ 4
  · intro w' hw'
    unfold packingWeight
    have h_part : G.cliqueFinset 3 = M ∪ externals G M := by
      ext t; simp only [Finset.mem_union, externals, Finset.mem_sdiff]
      constructor
      · intro ht; by_cases h : t ∈ M <;> [left; right] <;> [exact h; exact ⟨ht, h⟩]
      · intro h; rcases h with h | ⟨h, _⟩ <;> [exact hM.1.1 h; exact h]
    have h_disj : Disjoint M (externals G M) := by
      rw [Finset.disjoint_left]; intro t ht hext
      exact (Finset.mem_sdiff.mp hext).2 ht
    rw [h_part, Finset.sum_union h_disj]
    have hM_le : M.sum w' ≤ M.card := M_weight_le_card G M hM.1 w' hw'
    -- Exchange argument: optimal saturates M, then externals = 0
    sorry

end
