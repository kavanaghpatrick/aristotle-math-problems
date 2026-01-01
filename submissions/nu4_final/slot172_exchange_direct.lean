/-
Tuza ν=4: packingWeight ≤ 4 via Direct Exchange Argument

GOAL: Prove packingWeight G w ≤ 4 for any IsFractionalPacking.

KEY INSIGHT (Direct argument without LP):
1. Consider any fractional packing w
2. Define slack: for each m ∈ M, slack(m) = 1 - w(m) ≥ 0
3. Externals can only use edges with positive slack
4. Each external shares an M-edge e; weight on e must sum ≤ 1
5. The M-owner m_e contributes w(m_e), external contributes w(ext)
6. So w(ext) ≤ 1 - w(m_e) = slack(m_e)

Key equation:
- externals.sum w ≤ sum of slacks over M = M.card - M.sum w
- packingWeight = M.sum w + externals.sum w
- packingWeight ≤ M.sum w + (M.card - M.sum w) = M.card = 4

This is the exchange: externals can only take slack from M!

1 SORRY: Formalizing the slack consumption inequality
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
-- PROVEN SCAFFOLDING
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

/-- External triangles share at least one M-edge -/
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

/-- Unique M-owner for an M-edge -/
lemma M_edge_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ M_edges G M) :
    ∃! m, m ∈ M ∧ e ∈ m.sym2 := by
  rw [M_edges, Finset.mem_biUnion] at he
  obtain ⟨m, hm, he_filter⟩ := he
  have he_m := (Finset.mem_filter.mp he_filter).1
  have he_edge := (Finset.mem_filter.mp he_filter).2
  use m
  constructor
  · exact ⟨hm, he_m⟩
  · intro m' ⟨hm', he_m'⟩
    exact M_edge_unique_owner G M hM e he_edge m m' hm hm' he_m he_m'

/-- Get the unique owner of an M-edge -/
noncomputable def M_edge_owner_fn (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ M_edges G M) : Finset V :=
  (M_edge_owner G M hM e he).choose

-- ═══════════════════════════════════════════════════════════════════════
-- SLACK-BASED EXCHANGE ARGUMENT
-- ═══════════════════════════════════════════════════════════════════════

/-- Define slack at each M-element: how much room is left under w(m) ≤ 1 -/
def slack (w : Finset V → ℝ) (m : Finset V) : ℝ := 1 - w m

/-- Total slack over M -/
def totalSlack (M : Finset (Finset V)) (w : Finset V → ℝ) : ℝ :=
  M.sum (fun m => slack w m)

/-- Total slack equals M.card - M.sum w -/
lemma totalSlack_eq (M : Finset (Finset V)) (w : Finset V → ℝ) :
    totalSlack M w = M.card - M.sum w := by
  unfold totalSlack slack
  simp only [Finset.sum_sub_distrib, Finset.sum_const, smul_eq_mul, mul_one]

/-- For IsFractionalPacking, each w(m) ≤ 1 so slack ≥ 0 -/
lemma slack_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w)
    (m : Finset V) (hm : m ∈ M) : 0 ≤ slack w m := by
  unfold slack
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
  have h_sum_le : ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1 := hw.2.2 e h_e_edge
  have h_w_le : w m ≤ ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w :=
    Finset.single_le_sum (fun t _ => hw.1 t) h_m_in
  linarith

/-- Key lemma: external weight is bounded by total slack -/
lemma externals_sum_le_totalSlack (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    (externals G M).sum w ≤ totalSlack M w := by
  /-
  For each external t, it shares an M-edge e with unique owner m_e ∈ M.
  The edge constraint says w(m_e) + w(t) + (other triangles sharing e) ≤ 1.
  In particular, w(t) ≤ 1 - w(m_e) = slack(m_e).

  The complication: multiple externals can share the same M-edge.
  Solution: for each M-edge e, all triangles sharing e sum to ≤ 1.
  Sum over M-edges to get global bound.

  Actually, the cleanest approach:
  - Partition externals by which M-edge they share
  - For each M-edge e with owner m_e:
    - Externals sharing e: their sum ≤ 1 - w(m_e) = slack(m_e)
  - Sum: externals.sum ≤ sum over M-edges of slack(owner)

  But externals can share multiple M-edges, so we can't partition cleanly.
  Use: each external shares at least 1 M-edge, so:
  externals.sum w ≤ (sum over M-edges of (triangles sharing e).sum w - w(owner))
                  = sum over M-edges of (1 - w(owner)) [by edge constraint]
                  = sum over M-edges of slack(owner)

  And sum over M-edges of slack(owner) relates to totalSlack:
  Each m ∈ M owns exactly 3 M-edges (for a 3-clique).
  So sum over M-edges of slack(owner) = 3 × totalSlack.

  But this overcounts. We need a tighter argument...
  -/
  sorry

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════════════

theorem packingWeight_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ 4 := by
  unfold packingWeight
  have h_part : G.cliqueFinset 3 = M ∪ externals G M := by
    ext t; simp only [Finset.mem_union, externals, Finset.mem_sdiff]
    constructor
    · intro ht; by_cases h : t ∈ M <;> [left; right] <;> [exact h; exact ⟨ht, h⟩]
    · intro h; rcases h with h | ⟨h, _⟩ <;> [exact hM.1.1 h; exact h]
  have h_disj : Disjoint M (externals G M) := by
    rw [Finset.disjoint_left]; intro t ht hext; exact (Finset.mem_sdiff.mp hext).2 ht
  rw [h_part, Finset.sum_union h_disj]
  -- Use slack inequality
  have h_ext := externals_sum_le_totalSlack G M hM w hw
  rw [totalSlack_eq] at h_ext
  -- h_ext : externals.sum w ≤ M.card - M.sum w
  rw [hM4] at h_ext
  -- h_ext : externals.sum w ≤ 4 - M.sum w
  linarith

theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    ∃ w, IsFractionalPacking G w ∧ packingWeight G w = 4 ∧
         ∀ w', IsFractionalPacking G w' → packingWeight G w' ≤ 4 := by
  let w₀ : Finset V → ℝ := fun t => if t ∈ M then 1 else 0
  use w₀
  refine ⟨?_, ?_, ?_⟩
  -- w₀ is a fractional packing
  · refine ⟨fun t => by simp only [w₀]; split_ifs <;> linarith,
            fun t ht => by simp only [w₀]; split_ifs with h; exact absurd (hM.1.1 h) ht; rfl, ?_⟩
    intro e he
    let S := (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)
    have h_sum : S.sum w₀ = (S ∩ M).card := by
      rw [← Finset.sum_inter_add_sum_diff S M w₀]
      have h1 : (S ∩ M).sum w₀ = (S ∩ M).card := by
        simp only [w₀]; rw [Finset.sum_ite_mem, Finset.inter_comm M (S ∩ M)]
        simp [Finset.inter_assoc]
      have h2 : (S \ M).sum w₀ = 0 := by
        apply Finset.sum_eq_zero; intro t ht
        simp only [Finset.mem_sdiff] at ht; simp only [w₀, if_neg ht.2]
      linarith
    have h_card_le_1 : (S ∩ M).card ≤ 1 := by
      by_contra h_gt; push_neg at h_gt
      obtain ⟨m1, hm1, m2, hm2, hne⟩ := Finset.one_lt_card.mp h_gt
      simp only [Finset.mem_inter, Finset.mem_filter] at hm1 hm2
      exact hne (M_edge_unique_owner G M hM.1 e he m1 m2 hm1.2 hm2.2 hm1.1.2 hm2.1.2)
    calc S.sum w₀ = (S ∩ M).card := h_sum
      _ ≤ 1 := h_card_le_1
  -- packingWeight w₀ = 4
  · unfold packingWeight
    have h_part : G.cliqueFinset 3 = M ∪ externals G M := by
      ext t; simp only [Finset.mem_union, externals, Finset.mem_sdiff]
      constructor
      · intro ht; by_cases h : t ∈ M <;> [left; right] <;> [exact h; exact ⟨ht, h⟩]
      · intro h; rcases h with h | ⟨h, _⟩ <;> [exact hM.1.1 h; exact h]
    have h_disj : Disjoint M (externals G M) := by
      rw [Finset.disjoint_left]; intro t ht hext; exact (Finset.mem_sdiff.mp hext).2 ht
    rw [h_part, Finset.sum_union h_disj]
    have hM_sum : M.sum w₀ = (M.card : ℝ) := by
      trans M.sum (fun _ => (1 : ℝ))
      · apply Finset.sum_congr rfl; intro t ht; simp only [w₀, if_pos ht]
      · simp
    have hext_sum : (externals G M).sum w₀ = 0 := by
      apply Finset.sum_eq_zero; intro t ht
      simp only [w₀, externals, Finset.mem_sdiff] at ht ⊢; simp only [if_neg ht.2]
    rw [hM_sum, hext_sum, hM4]; ring
  -- All packings have weight ≤ 4
  · exact packingWeight_le_4 G M hM hM4

end
