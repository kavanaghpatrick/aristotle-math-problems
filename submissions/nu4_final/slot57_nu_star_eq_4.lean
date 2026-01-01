/-
slot57: Proving ν* = 4 for Cycle_4

INSIGHT FROM MULTI-AGENT DEBATE (Grok, Gemini, Dec 31 2025):
The key to proving τ ≤ 8 is showing ν* = 4 (not just ν* ≥ 4).

KEY LEMMA: Every triangle in G shares an edge with some M-triangle.

PROOF SKETCH:
1. At each shared vertex v_ab, any triangle through v_ab either:
   - IS A or B (the M-triangles at v_ab), or
   - Uses an edge of A or B (must share an edge with M)
2. This is because v_ab has adjacencies to: a_priv (from A), b_priv (from B),
   v_da (from A), v_bc (from B). Any triangle at v_ab uses two of these edges.
3. The only non-M-edge pairs at v_ab are {a_priv, b_priv}, {a_priv, v_bc},
   {b_priv, v_da}, {v_da, v_bc}. But these are "bridges" that don't form triangles
   with just v_ab (third vertex would need to be adjacent to both).

CONCLUSION:
- Every triangle shares an edge with M
- M_char saturates all M-edges (weight 1)
- Externals forced to weight 0
- Therefore ν* = 4
- By Krivelevich: τ ≤ 2ν* = 8
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot56)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- M-edges: all edges belonging to packing elements
def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (· ∈ G.edgeFinset))

-- ══════════════════════════════════════════════════════════════════════════════
-- FRACTIONAL PACKING (same as slot56)
-- ══════════════════════════════════════════════════════════════════════════════

def isFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, w t ≥ 0) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), w t ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  ∑ t ∈ G.cliqueFinset 3, w t

noncomputable def nu_star (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {x : ℝ | ∃ w, isFractionalPacking G w ∧ packingWeight G w = x}

def M_char (M : Finset (Finset V)) : Finset V → ℝ :=
  fun t => if t ∈ M then 1 else 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot54/55/56)
-- ══════════════════════════════════════════════════════════════════════════════

lemma M_char_nonneg (M : Finset (Finset V)) (t : Finset V) :
    M_char M t ≥ 0 := by
  unfold M_char; split_ifs <;> linarith

lemma M_char_zero_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∉ G.cliqueFinset 3) :
    M_char M t = 0 := by
  unfold M_char; split_ifs with h; · exfalso; exact ht (hM.1 h); · rfl

-- PROVEN by Aristotle in slot54 (UUID 1144f147)
lemma M_char_edge_sum_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), M_char M t ≤ 1 := by
  unfold M_char
  have h_edge_bound : (Finset.card (Finset.filter (fun t => e ∈ t.sym2) M)) ≤ 1 := by
    have h_edge_in_M : ∀ t1 t2 : Finset V, t1 ∈ M → t2 ∈ M → t1 ≠ t2 → ¬(e ∈ t1.sym2 ∧ e ∈ t2.sym2) := by
      intros t1 t2 ht1 ht2 hne h_edge
      have h_inter : (t1 ∩ t2).card ≤ 1 := hM.2 ht1 ht2 hne |> fun h => by simpa using h
      rcases e with ⟨ u, v ⟩ ; simp_all +decide [ Finset.ext_iff ]
      exact h_inter.not_lt ( Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩ )
    exact Finset.card_le_one.mpr fun t1 ht1 t2 ht2 => Classical.not_not.1 fun h =>
      h_edge_in_M t1 t2 ( Finset.filter_subset _ _ ht1 ) ( Finset.filter_subset _ _ ht2 ) h
      ⟨ Finset.mem_filter.mp ht1 |>.2, Finset.mem_filter.mp ht2 |>.2 ⟩
  simp_all +decide [ Finset.sum_ite ]
  exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_edge_bound

lemma M_char_is_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    isFractionalPacking G (M_char M) :=
  ⟨M_char_nonneg M, M_char_zero_outside G M hM, fun e he => M_char_edge_sum_le_1 G M hM e he⟩

lemma M_char_weight_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    packingWeight G (M_char M) = M.card := by
  unfold packingWeight M_char
  have h_split : ∑ t ∈ G.cliqueFinset 3, (if t ∈ M then (1 : ℝ) else 0) = ∑ t ∈ M, (1 : ℝ) := by
    rw [← Finset.sum_filter]; congr 1; ext t; simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, ht⟩ => ht, fun ht => ⟨hM.1 ht, ht⟩⟩
  rw [h_split]; simp

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every triangle shares an edge with M
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key structural lemma: Every triangle in G shares at least one edge
    with some element of the maximal packing M.

    This follows from maximality: if a triangle T shared NO edge with M,
    then T would be edge-disjoint from all elements of M, contradicting
    maximality (we could add T to the packing).
-/
lemma triangle_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (T.sym2 ∩ m.sym2).Nonempty := by
  -- By contradiction: if T shares no edge with any m ∈ M
  by_contra h_no_share
  push_neg at h_no_share
  -- Then T is edge-disjoint from all m ∈ M
  have h_disjoint : ∀ m ∈ M, (T ∩ m).card ≤ 1 := by
    intro m hm
    -- If they share 2+ vertices, they share an edge
    by_contra h_share_2
    push_neg at h_share_2
    have h_inter_card : 2 ≤ (T ∩ m).card := h_share_2
    -- Extract two vertices from intersection
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (Nat.one_lt_iff_ne_one.mpr
      (Nat.lt_of_lt_of_le Nat.one_lt_two h_inter_card |> fun h => Nat.ne_of_gt h))
    have hu_T : u ∈ T := Finset.mem_inter.mp hu |>.1
    have hu_m : u ∈ m := Finset.mem_inter.mp hu |>.2
    have hv_T : v ∈ T := Finset.mem_inter.mp hv |>.1
    have hv_m : v ∈ m := Finset.mem_inter.mp hv |>.2
    -- The edge {u,v} is in both T.sym2 and m.sym2
    have h_edge_shared : s(u, v) ∈ T.sym2 ∩ m.sym2 := by
      simp only [Finset.mem_inter, Finset.mem_sym2, Sym2.mem_iff]
      exact ⟨⟨Or.inl hu_T, Or.inl hv_T⟩, ⟨Or.inl hu_m, Or.inl hv_m⟩⟩
    -- Contradiction with h_no_share
    exact h_no_share m hm ⟨s(u, v), h_edge_shared⟩
  -- Now M ∪ {T} is a valid packing
  have h_T_not_in_M : T ∉ M := by
    intro hT_in_M
    -- T ∩ T = T, which has card 3, not ≤ 1
    have := h_disjoint T hT_in_M
    simp only [Finset.inter_self] at this
    -- T has 3 vertices since it's a triangle
    have hT_card : T.card = 3 := by
      have := SimpleGraph.mem_cliqueFinset_iff.mp hT
      exact this.card_eq
    omega
  have h_larger : isTrianglePacking G (insert T M) := by
    constructor
    · -- All are triangles
      intro t ht
      simp only [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exact hT
      · exact hM.1.1 ht
    · -- Pairwise edge-disjoint
      intro t1 ht1 t2 ht2 hne
      simp only [Finset.coe_insert, Set.mem_insert_iff] at ht1 ht2
      rcases ht1 with rfl | ht1 <;> rcases ht2 with rfl | ht2
      · exact (hne rfl).elim
      · exact h_disjoint t2 ht2
      · have := h_disjoint t1 ht1
        rw [Finset.inter_comm] at this
        exact this
      · exact hM.1.2 ht1 ht2 hne
  -- This contradicts maximality of M
  have h_card_larger : (insert T M).card > M.card := by
    rw [Finset.card_insert_of_not_mem h_T_not_in_M]
    omega
  -- M.card = trianglePackingNumber G, so no larger packing exists
  have h_max : M.card = trianglePackingNumber G := hM.2
  -- But insert T M is a larger valid packing, contradiction
  sorry -- Aristotle should be able to finish this from the definitions

-- ══════════════════════════════════════════════════════════════════════════════
-- CONSEQUENCE: External triangles have weight 0 in optimal fractional packing
-- ══════════════════════════════════════════════════════════════════════════════

/-- If M_char saturates all M-edges (weight 1 on each M-triangle),
    then external triangles must have weight 0 in any optimal packing
    extending M_char, because they share M-edges that are already saturated. -/
lemma external_weight_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_not_M : T ∉ M)
    (w : Finset V → ℝ) (hw : isFractionalPacking G w)
    (hw_M : ∀ m ∈ M, w m = 1) :
    w T = 0 := by
  -- T shares an edge with some m ∈ M
  obtain ⟨m, hm, e, he⟩ := triangle_shares_edge_with_M G M hM T hT
  -- That edge is saturated by w m = 1
  have he_in_T : e ∈ T.sym2 := Finset.mem_inter.mp he |>.1
  have he_in_m : e ∈ m.sym2 := Finset.mem_inter.mp he |>.2
  -- The edge e is in G.edgeFinset (since m is a triangle in G)
  have he_in_G : e ∈ G.edgeFinset := by
    have hm_tri := hM.1.1 hm
    have := SimpleGraph.mem_cliqueFinset_iff.mp hm_tri
    sorry -- e ∈ m.sym2 and m is a clique in G implies e is an edge
  -- The fractional constraint at e: sum of weights ≤ 1
  have h_constraint := hw.2.2 e he_in_G
  -- w m = 1 is included in this sum
  have h_w_m_in_sum : w m ≤ ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), w t := by
    apply Finset.single_le_sum
    · intro t _; exact hw.1 t
    · simp only [Finset.mem_filter]
      exact ⟨hM.1.1 hm, he_in_m⟩
  -- Since w m = 1, the sum is at least 1
  have h_sum_ge_1 : ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), w t ≥ 1 := by
    calc ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), w t
        ≥ w m := h_w_m_in_sum
      _ = 1 := hw_M m hm
  -- But sum ≤ 1 by constraint, so sum = 1 exactly
  have h_sum_eq_1 : ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), w t = 1 := by
    linarith
  -- Since w m = 1 accounts for the entire sum, all other weights are 0
  have h_T_in_filter : T ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) := by
    simp only [Finset.mem_filter]
    exact ⟨hT, he_in_T⟩
  -- w T ≥ 0 and the sum is tight at 1 with w m = 1
  -- Since T ≠ m and w m = 1, w T must be 0
  sorry -- Aristotle should be able to finish this

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN RESULT: ν* = 4 for Cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- The fractional packing number equals 4 for graphs with Cycle_4 packing. -/
theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    nu_star G = 4 := by
  -- Lower bound: M_char achieves weight 4
  have h_lower : nu_star G ≥ 4 := by
    have hw : isFractionalPacking G (M_char M) := M_char_is_fractional G M hM.1
    have hw_weight : packingWeight G (M_char M) = 4 := by
      rw [M_char_weight_eq_card G M hM.1]
      have hM_eq : M = {A, B, C, D} := hcycle.1
      rw [hM_eq]
      have hAB : A ≠ B := hcycle.2.1
      have hBC : B ≠ C := hcycle.2.2.1
      have hCD : C ≠ D := hcycle.2.2.2.1
      have hAC : A ≠ C := hcycle.2.2.2.2.1
      have hAD : A ≠ D := hcycle.2.2.2.2.2.1
      have hBD : B ≠ D := hcycle.2.2.2.2.2.2.1
      simp only [Finset.card_insert_of_not_mem, Finset.card_singleton,
                 Finset.mem_insert, Finset.mem_singleton, not_or]
      simp_all
    unfold nu_star
    apply le_csSup
    · -- Bounded above (by number of triangles / 3 edges per triangle)
      use (G.cliqueFinset 3).card
      intro x ⟨w, hw', hx⟩
      rw [← hx]
      unfold packingWeight
      sorry -- Standard bound: fractional packing ≤ number of triangles
    · exact ⟨M_char M, hw, hw_weight⟩
  -- Upper bound: no fractional packing can exceed 4
  have h_upper : nu_star G ≤ 4 := by
    unfold nu_star
    apply csSup_le
    · -- Non-empty
      exact ⟨4, M_char M, M_char_is_fractional G M hM.1, by
        rw [M_char_weight_eq_card G M hM.1]
        have hM_eq : M = {A, B, C, D} := hcycle.1
        rw [hM_eq]
        have hAB : A ≠ B := hcycle.2.1
        have hBC : B ≠ C := hcycle.2.2.1
        have hCD : C ≠ D := hcycle.2.2.2.1
        have hAC : A ≠ C := hcycle.2.2.2.2.1
        have hAD : A ≠ D := hcycle.2.2.2.2.2.1
        have hBD : B ≠ D := hcycle.2.2.2.2.2.2.1
        simp only [Finset.card_insert_of_not_mem, Finset.card_singleton,
                   Finset.mem_insert, Finset.mem_singleton, not_or]
        simp_all⟩
    · -- Every fractional packing has weight ≤ 4
      intro x ⟨w, hw, hx⟩
      rw [← hx]
      -- The key: M-edges form a "tight" structure
      -- Each edge is in at most one M-triangle, and external triangles
      -- share M-edges, so total weight ≤ 4
      sorry -- Aristotle should prove this from external_weight_zero
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- KRIVELEVICH BOUND (Literature)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Krivelevich (1995): τ(G) ≤ 2·ν*(G) -/
theorem krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * nu_star G := by
  sorry -- Literature result (Krivelevich 1995, Discrete Math 142:281-286)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for Cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  have h_nu_star : nu_star G = 4 := nu_star_eq_4 G M hM A B C D hcycle
  have h_kriv := krivelevich_bound G
  have h2 : (triangleCoveringNumber G : ℝ) ≤ 8 := by
    calc (triangleCoveringNumber G : ℝ)
        ≤ 2 * nu_star G := h_kriv
      _ = 2 * 4 := by rw [h_nu_star]
      _ = 8 := by ring
  exact Nat.cast_le.mp (by linarith : (triangleCoveringNumber G : ℝ) ≤ 8)

end
