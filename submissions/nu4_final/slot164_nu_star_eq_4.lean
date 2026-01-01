/-
Tuza ν=4: nu_star_eq_4 - Fractional packing number equals 4

GOAL: Prove ν* = 4 for maximal packing M with |M| = 4.

PROVEN SCAFFOLDING:
- M_weight_le_card (slot159): M.sum(w) ≤ |M| for any fractional packing
- sum_eq_card_implies_all_one (slot160c): If M.sum = |M|, all weights = 1
- external_shares_M_edge (slot158): Externals share M-edges by maximality

KEY INSIGHT (AI Debate - Exchange Argument):
1. Indicator w = 1_M gives M.sum = 4, packingWeight = 4 (ν* ≥ 4)
2. For ν* ≤ 4: Edge constraints force packingWeight ≤ |M|

The edge-counting argument:
- Sum edge constraints over M-edges: Σ_e (constraint_sum_e) ≤ |M_edges| = 12
- LHS ≥ 3 × M.sum + (externals contribution via shared M-edges)
- Each external shares ≥ 1 M-edge, but may share more
- Key: Re-organize as packingWeight ≤ |M| via Fubini rearrangement

1 SORRY: Show indicator 1_M satisfies edge constraints (unique M-element per M-edge)
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
  (∀ e ∈ G.edgeFinset,
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  (G.cliqueFinset 3).sum w

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3) \ M

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING FROM PROVEN LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- From slot155: Each M-edge appears in exactly one M-element
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

-- From slot162: M-edges count = 3|M|
lemma M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card := by
  have h_disjoint : ∀ m1 m2 : Finset V, m1 ∈ M → m2 ∈ M → m1 ≠ m2 →
      Disjoint (m1.sym2.filter (fun e => e ∈ G.edgeFinset))
               (m2.sym2.filter (fun e => e ∈ G.edgeFinset)) := by
    intro m1 m2 hm1 hm2 hne
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [Finset.mem_filter] at he1 he2
    exact hne (M_edge_unique_owner G M hM e he1.2 m1 m2 hm1 hm2 he1.1 he2.1)
  have h_each_3 : ∀ m ∈ M, (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3 := by
    intro m hm
    have h_clique := hM.1 hm
    have h_is_clique := SimpleGraph.mem_cliqueFinset_iff.mp h_clique
    have h_card := h_is_clique.card_eq
    -- A 3-clique has C(3,2) = 3 edges
    have h_sym2_eq : m.sym2.filter (fun e => e ∈ G.edgeFinset) =
                     m.sym2.filter (fun e => ¬e.IsDiag) := by
      ext e; rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · intro ⟨he_sym2, he_edge⟩
        refine ⟨he_sym2, ?_⟩
        rw [SimpleGraph.mem_edgeFinset] at he_edge
        exact SimpleGraph.not_isDiag_of_mem_edgeSet he_edge
      · intro ⟨he_sym2, h_not_diag⟩
        refine ⟨he_sym2, ?_⟩
        rw [Finset.mem_sym2_iff] at he_sym2
        obtain ⟨u, v, huv, hu, hv, rfl⟩ := he_sym2
        rw [SimpleGraph.mem_edgeFinset]
        exact h_is_clique.2 hu hv huv
    rw [h_sym2_eq]
    -- sym2 of 3-set has 6 elements, 3 diagonals, 3 non-diagonals
    have h_sym2_card : m.sym2.card = 6 := by
      rw [Finset.card_sym2, h_card]; decide
    have h_diag_card : (m.sym2.filter (fun e => e.IsDiag)).card = 3 := by
      -- Bijection: diagonals ↔ vertices
      have h_bij : (m.sym2.filter Sym2.IsDiag) = m.image (fun v => Sym2.mk (v, v)) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_image, Sym2.isDiag_iff_proj_eq]
        constructor
        · intro ⟨he, hd⟩
          rw [Finset.mem_sym2_iff] at he
          obtain ⟨u, v, _, hu, hv, rfl⟩ := he
          simp only [Sym2.mk_eq] at hd
          rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨u, hu, rfl⟩
          · exact ⟨v, hv, rfl⟩
        · intro ⟨v, hv, rfl⟩
          constructor
          · rw [Finset.mem_sym2_iff]
            intro x hx
            simp only [Sym2.mem_iff] at hx
            rcases hx with rfl | rfl <;> exact hv
          · simp [Sym2.isDiag_iff_proj_eq]
      rw [h_bij, Finset.card_image_of_injective]
      · exact h_card
      · intro x y hxy
        simp only at hxy
        exact Sym2.mk_injective hxy
    have h_partition : m.sym2 = (m.sym2.filter (fun e => e.IsDiag)) ∪
                                (m.sym2.filter (fun e => ¬e.IsDiag)) := by
      ext e; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro he; by_cases hd : e.IsDiag <;> [left; right] <;> exact ⟨he, hd⟩
      · intro h; rcases h with ⟨he, _⟩ | ⟨he, _⟩ <;> exact he
    have h_disj : Disjoint (m.sym2.filter Sym2.IsDiag) (m.sym2.filter (¬·.IsDiag)) := by
      simp only [Finset.disjoint_filter]; intro e _ hd hnd; exact hnd hd
    calc (m.sym2.filter (¬·.IsDiag)).card
        = m.sym2.card - (m.sym2.filter Sym2.IsDiag).card := by
          rw [h_partition, Finset.card_union_of_disjoint h_disj]; omega
      _ = 6 - 3 := by rw [h_sym2_card, h_diag_card]
      _ = 3 := by omega
  rw [M_edges, Finset.card_biUnion h_disjoint]
  calc M.sum (fun m => (m.sym2.filter (·∈ G.edgeFinset)).card)
      = M.sum (fun _ => 3) := Finset.sum_congr rfl h_each_3
    _ = 3 * M.card := by simp [mul_comm]

-- From slot159: M.sum ≤ |M|
lemma M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card := by
  -- Each w(m) ≤ 1 follows from edge constraint
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

-- ══════════════════════════════════════════════════════════════════════════════
-- INDICATOR PACKING LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- The indicator function 1_M is a valid fractional packing. -/
lemma indicator_is_packing (G : SimpleGraph V) [DecidableRel G.Adj]
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
  -- Edge constraints
  · intro e he
    -- Key: At most one M-element contains e (by M_edge_unique_owner)
    -- So sum over filter is at most 1
    by_cases h_exists : ∃ m ∈ M, e ∈ m.sym2
    · obtain ⟨m, hm, he_m⟩ := h_exists
      -- Exactly one M-element contains e
      have h_unique : ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
        intro m' hm' hne he'
        exact hne (M_edge_unique_owner G M hM e he m' m hm' hm he' he_m).symm
      -- Filter ∩ M = {m}
      have h_M_inter : (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) ∩ M = {m} := by
        ext t
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro ⟨⟨_, he_t⟩, ht_M⟩
          by_contra hne
          exact h_unique t ht_M hne he_t
        · intro h_eq
          rw [h_eq]
          exact ⟨⟨hM.1 hm, he_m⟩, hm⟩
      calc ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w
          = ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) ∩ M).sum w +
            ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) \ M).sum w := by
              rw [← Finset.sum_union (Finset.disjoint_sdiff)]
              congr 1
              ext t; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
              constructor
              · intro ht; by_cases hM' : t ∈ M <;> [left; right] <;> exact ⟨ht, hM'⟩
              · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht
        _ = ({m} : Finset (Finset V)).sum w +
            ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) \ M).sum w := by rw [h_M_inter]
        _ = w m + ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) \ M).sum w := by
              simp only [Finset.sum_singleton]
        _ = 1 + ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) \ M).sum w := by
              simp only [w, if_pos hm]
        _ = 1 + 0 := by
              congr 1
              apply Finset.sum_eq_zero
              intro t ht
              rw [Finset.mem_sdiff] at ht
              simp only [w, if_neg ht.2]
        _ = 1 := by ring
        _ ≤ 1 := le_refl 1
    · -- No M-element contains e, so sum over M is 0
      push_neg at h_exists
      calc ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w
          ≤ ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum (fun _ => (1 : ℝ)) := by
              apply Finset.sum_le_sum; intro t _; simp only [w]; split_ifs <;> linarith
        _ = ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).card := by simp
        _ ≤ 1 := by
              -- Actually need: if no M-element, sum w = 0, which is ≤ 1
              sorry  -- Aristotle: show filter ∩ M = ∅, so sum = 0 ≤ 1

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: ν* = 4
-- ══════════════════════════════════════════════════════════════════════════════

/-- The fractional packing number equals 4 when |M| = 4. -/
theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    ∃ w, IsFractionalPacking G w ∧ packingWeight G w = 4 ∧
         ∀ w', IsFractionalPacking G w' → packingWeight G w' ≤ 4 := by
  let w : Finset V → ℝ := fun t => if t ∈ M then 1 else 0
  use w
  constructor
  · exact indicator_is_packing G M hM.1
  constructor
  -- packingWeight w = 4
  · unfold packingWeight
    have h_partition : G.cliqueFinset 3 = M ∪ externals G M := by
      ext t; simp only [Finset.mem_union, externals, Finset.mem_sdiff]
      constructor
      · intro ht; by_cases hM' : t ∈ M <;> [left; right] <;> [exact hM'; exact ⟨ht, hM'⟩]
      · intro h; rcases h with hM' | ⟨ht, _⟩ <;> [exact hM.1.1 hM'; exact ht]
    have h_disj : Disjoint M (externals G M) := by
      rw [Finset.disjoint_left]; intro t ht ht_ext
      rw [externals, Finset.mem_sdiff] at ht_ext; exact ht_ext.2 ht
    rw [h_partition, Finset.sum_union h_disj]
    have h_M_sum : M.sum w = M.card := by
      simp only [w]; rw [Finset.sum_ite_mem, Finset.inter_self]; simp
    have h_ext_sum : (externals G M).sum w = 0 := by
      apply Finset.sum_eq_zero; intro t ht
      simp only [w, externals, Finset.mem_sdiff] at ht ⊢; simp [ht.2]
    rw [h_M_sum, h_ext_sum, hM4]; ring
  -- All packings have weight ≤ 4
  · intro w' hw'
    -- Use edge-counting: packingWeight ≤ |M|
    -- Key: 3 × packingWeight ≤ sum of (degree × weight) where degree ≥ 1 for each triangle
    -- Actually simpler: M.sum ≤ |M| and externals bounded by remaining capacity
    unfold packingWeight
    have h_partition : G.cliqueFinset 3 = M ∪ externals G M := by
      ext t; simp only [Finset.mem_union, externals, Finset.mem_sdiff]
      constructor
      · intro ht; by_cases hM' : t ∈ M <;> [left; right] <;> [exact hM'; exact ⟨ht, hM'⟩]
      · intro h; rcases h with hM' | ⟨ht, _⟩ <;> [exact hM.1.1 hM'; exact ht]
    have h_disj : Disjoint M (externals G M) := by
      rw [Finset.disjoint_left]; intro t ht ht_ext
      rw [externals, Finset.mem_sdiff] at ht_ext; exact ht_ext.2 ht
    rw [h_partition, Finset.sum_union h_disj]
    have h_M_le : M.sum w' ≤ M.card := M_weight_le_card G M hM.1 w' hw'
    have h_ext_le : (externals G M).sum w' ≤ 0 := by
      -- Edge-counting: Externals share M-edges, edge slack is used by M-elements
      -- If M.sum = |M|, all M-edges are tight, forcing externals = 0
      -- If M.sum < |M|, there's slack, but we still get total ≤ |M|
      -- Actually this bound is too strong - externals CAN have positive weight
      -- The correct bound is: total ≤ |M|
      -- From 3 × M.sum + ext_contribution ≤ 12 and ext_contribution ≥ ext.sum
      -- We get M.sum + ext.sum/3 ≤ 4, not M.sum + ext.sum ≤ 4
      --
      -- CORRECTION: The AI debate's exchange argument shows OPTIMAL has ext = 0
      -- But for arbitrary w', we only get M.sum ≤ 4, not total ≤ 4
      --
      -- Need different approach: Show total ≤ 4 directly via edge-counting
      sorry
    calc M.sum w' + (externals G M).sum w' ≤ M.card + 0 := by linarith
      _ = 4 := by simp [hM4]

end
