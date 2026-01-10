/-
  slot225_bridge_externals_share_apex.lean

  THE MAKE-OR-BREAK LEMMA FOR tau <= 8 (Multi-Agent Debate, Jan 4, 2026)

  Question: Do externals of DIFFERENT M-elements at a shared vertex share a common apex?

  CONTEXT:
  - slot182 PROVEN: Two externals of SAME M-element share an edge (5-packing argument)
  - slot224f PROVEN: Externals using DIFFERENT edges of SAME M-element share external vertex
  - THIS LEMMA: T1 external of A, T2 external of B (DIFFERENT M-elements) at shared v

  KEY INSIGHT FROM DEBATE:
  The naive 5-packing argument does NOT directly work because:
  - T1 is external of A (shares edge with A, not B, C, D)
  - T2 is external of B (shares edge with B, not A, C, D)
  - M' = (M \ {A, B}) cup {T1, T2} = {T1, T2, C, D} has only 4 elements
  - No immediate 5-packing contradiction!

  PROOF STRATEGIES FOR ARISTOTLE:

  Strategy 1 (Modified 5-packing):
  - Suppose T1, T2 don't share an edge (hence share at most 1 vertex = v)
  - Consider M' = {T1, T2, C, D}
  - Check pairwise intersections:
    * T1 inter T2 = {v} (by assumption) <= 1 CHECK
    * T1 inter C <= 1 (T1 external of A, doesn't share edge with C)
    * T1 inter D <= 1 (T1 external of A, doesn't share edge with D)
    * T2 inter C <= 1 (T2 external of B, doesn't share edge with C)
    * T2 inter D <= 1 (T2 external of B, doesn't share edge with D)
    * C inter D <= 1 (from M being a packing)
  - So M' might be a valid 4-packing
  - But M' != M since T1, T2 not in M, and A, B not in M'
  - This doesn't immediately contradict nu = 4...
  - UNLESS we can show M' is "strictly better" in some way

  Strategy 2 (Maximality violation):
  - Since T1 not in M but T1 in cliqueFinset 3, by maximality of M:
    there exists X in M with |T1 inter X| >= 2
  - Since T1 is external of A: |T1 inter A| >= 2 (shares edge with A)
  - Since T1 is external of A: for B, C, D in M with B != A: |T1 inter B| <= 1
  - So the X must be A
  - Similarly for T2: the X must be B
  - Now what?

  Strategy 3 (6-packing attempt):
  - If T1 inter T2 = {v} only, consider M'' = M cup {T1}... but |T1 inter A| >= 2
  - That violates packing property!
  - So M cup {T1} is NOT a valid packing
  - However, (M \ {A}) cup {T1} = {T1, B, C, D} might be valid 4-packing
  - This is just another way of saying the same thing...

  Strategy 4 (Direct vertex counting):
  - T1 = {v, a, x1} where a in A, x1 not in A (external vertex of T1)
  - T2 = {v, b, x2} where b in B, x2 not in B (external vertex of T2)
  - Since A inter B = {v} in cycle_4: a != b (a in A \ B, b in B \ A)
  - If x1 != x2, then T1 inter T2 = {v}
  - Now consider adjacencies in G:
    * G.Adj v a and G.Adj v x1 and G.Adj a x1 (T1 is triangle)
    * G.Adj v b and G.Adj v x2 and G.Adj b x2 (T2 is triangle)
  - If x1 = x2, we're done
  - If x1 != x2, what additional constraint forces contradiction?

  Strategy 5 (THE KEY INSIGHT - 6-packing from cross externals):
  - We have T1 external of A at v, T2 external of B at v
  - Suppose x1 != x2 (different apexes)
  - Then T1 inter T2 = {v} only
  - Now consider:
    * Does T2 share edge with A? T2 external of B, so T2 doesn't share edge with A
    * But T2 contains v and v in A! Does T2 contain another vertex of A?
    * If yes, T2 shares edge with A (contradiction since T2 external of B only)
    * If no, T2 inter A = {v} only
  - Similarly T1 inter B = {v} only
  - Now the 6-triangle set {A, B, C, D, T1, T2}:
    * A inter T1 >= 2 (T1 shares edge with A) - VIOLATES packing!
  - Wait, that means {A, B, C, D, T1} is not a valid 5-packing anyway
  - So we can't build a larger packing this way...

  Strategy 6 (Alternative packing construction):
  - Consider {T1, T2, C, D} - this might be a valid 4-packing if:
    * T1 inter T2 <= 1 (need to prove or assume)
    * T1 inter C <= 1 (external of A doesn't share with C)
    * T1 inter D <= 1 (external of A doesn't share with D)
    * T2 inter C <= 1 (external of B doesn't share with C)
    * T2 inter D <= 1 (external of B doesn't share with D)
    * C inter D <= 1 (M is packing)
  - If this is valid 4-packing and M is maximal 4-packing...
  - Then {T1, T2, C, D} should also be maximal
  - But A is a triangle that shares edge with T1...
  - So A inter T1 >= 2, meaning {T1, T2, C, D} is NOT maximal!
  - Wait, that's the contradiction: {T1, T2, C, D} can't be maximal
  - because A blocks it (A not in the set, but A inter T1 >= 2)
  - Hmm, but M also satisfies this (every triangle not in M intersects some element >= 2)
  - So this doesn't give contradiction either...

  CRITICAL REALIZATION:
  The lemma might actually be FALSE. Pattern 6 in FALSE_LEMMAS.md suggests
  external_share_common_vertex is false, and this might extend to bridge externals.

  ARISTOTLE: Try to prove it OR find a counterexample graph.

  1 SORRY for Aristotle.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ==============================================================================
-- DEFINITIONS (standard from proven files)
-- ==============================================================================

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

/-- External triangle: in G's cliques, not in M, shares edge with A only -/
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ==============================================================================
-- PROVEN SCAFFOLDING LEMMAS (from slot182, slot224f)
-- ==============================================================================

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  have hu_inter : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu_m⟩
  have hv_inter : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv_m⟩
  exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact h_not_share ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  have ht_3 : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht_ext.1 |>.2
  have hB_3 : B.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hB) |>.2
  exact not_share_implies_one_vertex t B ht_3 hB_3 (ht_ext.2.2.2 B hB hAB.symm)

lemma edge_disjoint_implies_one_vertex (T₁ T₂ : Finset V)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    (T₁ ∩ T₂).card ≤ 1 := by
  have h_not_share : ¬sharesEdgeWith T₁ T₂ := fun ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩ =>
    h_edge_disj u v huv hu₁ hv₁ hu₂ hv₂
  exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_not_share

-- ==============================================================================
-- 5-PACKING CONSTRUCTION (PROVEN in slot180)
-- ==============================================================================

theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M' := by
  let M_minus_A := M.erase A
  let M' := {T₁, T₂} ∪ M_minus_A
  use M'
  have hT₁_not_M : T₁ ∉ M := hT₁.2.1
  have hT₂_not_M : T₂ ∉ M := hT₂.2.1
  have hM_minus_A_card : M_minus_A.card = 3 := by rw [Finset.card_erase_of_mem hA]; omega
  have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
  have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
  constructor
  · have hT₁_not_MA : T₁ ∉ M_minus_A := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MA : T₂ ∉ M_minus_A := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem]; simp [hT₁_ne_T₂]; simp [hT₁_ne_T₂]
    have h_disj : Disjoint {T₁, T₂} M_minus_A := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact fun h => hT₁_not_MA (h ▸ hy);
                                    exact fun h => hT₂_not_MA (h ▸ hy)]
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_A_card]
  · constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht_pair | ht_MA
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MA).2
    · intro t₁ ht₁ t₂ ht₂ h_ne
      rcases Finset.mem_union.mp ht₁ with ht₁_pair | ht₁_MA <;>
      rcases Finset.mem_union.mp ht₂ with ht₂_pair | ht₂_MA
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne
          · rw [Finset.mem_singleton] at ht₂_sing; rw [heq₁, ht₂_sing]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂, Finset.inter_comm]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne
      · have hB_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        have hB_ne_A : t₂ ≠ A := (Finset.mem_erase.mp ht₂_MA).1
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]; exact external_intersects_other_le_1 G M hM A t₂ hB_M hB_ne_A.symm T₁ hT₁
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          exact external_intersects_other_le_1 G M hM A t₂ hB_M hB_ne_A.symm T₂ hT₂
      · have hB_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have hB_ne_A : t₁ ≠ A := (Finset.mem_erase.mp ht₁_MA).1
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂, Finset.inter_comm]
          exact external_intersects_other_le_1 G M hM A t₁ hB_M hB_ne_A.symm T₁ hT₁
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing, Finset.inter_comm]
          exact external_intersects_other_le_1 G M hM A t₁ hB_M hB_ne_A.symm T₂ hT₂
      · exact hM.1.2 (Finset.mem_erase.mp ht₁_MA).2 (Finset.mem_erase.mp ht₂_MA).2 h_ne

-- ==============================================================================
-- PROVEN: Two externals of SAME M-element share edge (slot182)
-- ==============================================================================

theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  have h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False :=
    fun u v huv hu₁ hv₁ hu₂ hv₂ => h_no_edge ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_edge_disj
  have h_bound := hν M' hM'_packing
  omega

-- ==============================================================================
-- HELPER: Unique external vertex
-- ==============================================================================

lemma external_has_unique_outside_vertex (T A : Finset V)
    (hT_3 : T.card = 3) (hTA : (T ∩ A).card = 2) :
    ∃! x, x ∈ T ∧ x ∉ A := by
  have h_diff : (T \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T A
    omega
  rw [Finset.card_eq_one] at h_diff
  obtain ⟨x, hx_eq⟩ := h_diff
  use x
  constructor
  · have hx_mem : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact ⟨Finset.mem_sdiff.mp hx_mem |>.1, Finset.mem_sdiff.mp hx_mem |>.2⟩
  · intro y ⟨hy_T, hy_not_A⟩
    have : y ∈ T \ A := Finset.mem_sdiff.mpr ⟨hy_T, hy_not_A⟩
    rw [hx_eq] at this
    exact Finset.mem_singleton.mp this

-- ==============================================================================
-- KEY STRUCTURAL LEMMA: External at v only shares v with non-owner M-elements
-- ==============================================================================

/-- If T is external of A containing v, and v in B where B != A,
    then T inter B = {v} (only the shared vertex). -/
lemma external_inter_nonowner_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_v : v ∈ T)
    (hT_3 : T.card = 3) :
    T ∩ B = {v} := by
  have hB_3 : B.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hB) |>.2
  -- T doesn't share edge with B (external of A only)
  have hT_not_B : ¬sharesEdgeWith T B := hT.2.2.2 B hB hAB.symm
  have hT_B_le_1 : (T ∩ B).card ≤ 1 := not_share_implies_one_vertex T B hT_3 hB_3 hT_not_B
  -- But v in T inter B
  have hv_inter : v ∈ T ∩ B := Finset.mem_inter.mpr ⟨hT_v, hv_B⟩
  -- So T inter B = {v}
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · exact hv_inter
  · intro y hy
    by_contra h_ne
    have h_two : ({v, y} : Finset V) ⊆ T ∩ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hv_inter
      · exact hy
    have h_card : ({v, y} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      exact h_ne.symm
    have := Finset.card_le_card h_two
    omega

-- ==============================================================================
-- HELPER: External at v has structure {v, a, x} with a in A, x not in A
-- ==============================================================================

lemma external_structure_at_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M)
    (v : V) (hv_A : v ∈ A)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_v : v ∈ T)
    (hT_3 : T.card = 3) :
    ∃ a x : V, a ∈ A ∧ x ∉ A ∧ a ≠ v ∧ x ≠ v ∧ a ≠ x ∧ T = {v, a, x} := by
  -- T shares edge with A, so |T inter A| >= 2
  have hT_A := shares_edge_implies_two_vertices T A hT.2.2.1
  have hA_3 : A.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hA) |>.2
  -- |T inter A| <= 2 (otherwise T = A, but T not in M)
  have hT_A_le : (T ∩ A).card ≤ 2 := by
    by_contra h
    push_neg at h
    have h_sub : T ⊆ A := by
      have h_eq : (T ∩ A).card = T.card := by
        have h1 : (T ∩ A).card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
        linarith
      exact Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq h_eq.symm)
    have h_eq_A : T = A := Finset.eq_of_subset_of_card_le h_sub (by rw [hT_3, hA_3])
    exact hT.2.1 (h_eq_A ▸ hA)
  have hT_A_eq : (T ∩ A).card = 2 := by omega
  -- Get the two vertices in T inter A
  obtain ⟨u₁, u₂, h_ne_12, h_eq⟩ := Finset.card_eq_two.mp hT_A_eq
  -- One of them is v
  have hv_in : v ∈ T ∩ A := Finset.mem_inter.mpr ⟨hT_v, hv_A⟩
  rw [h_eq] at hv_in
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv_in
  -- Get the third vertex (external)
  have h_diff : (T \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T A
    omega
  obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp h_diff
  have hx_T : x ∈ T := by
    have : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.1
  have hx_not_A : x ∉ A := by
    have : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.2
  -- Get a as the other vertex in T inter A
  rcases hv_in with rfl | rfl
  · -- v = u₁, so a = u₂
    use u₂, x
    have hu₂_A : u₂ ∈ A := by rw [← h_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    have hu₂_T : u₂ ∈ T := by rw [← h_eq]; simp
    have hx_ne_v : x ≠ v := fun heq => hx_not_A (heq ▸ hv_A)
    have hx_ne_u₂ : x ≠ u₂ := fun heq => hx_not_A (heq ▸ hu₂_A)
    refine ⟨hu₂_A, hx_not_A, h_ne_12.symm, hx_ne_v, hx_ne_u₂.symm, ?_⟩
    -- T = {v, u₂, x}
    ext y
    constructor
    · intro hy
      by_cases hy_A : y ∈ A
      · have : y ∈ T ∩ A := Finset.mem_inter.mpr ⟨hy, hy_A⟩
        rw [h_eq] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · simp
        · simp
      · have : y ∈ T \ A := Finset.mem_sdiff.mpr ⟨hy, hy_A⟩
        rw [hx_eq] at this
        simp only [Finset.mem_singleton] at this
        simp [this]
    · intro hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hT_v
      · exact hu₂_T
      · exact hx_T
  · -- v = u₂, so a = u₁
    use u₁, x
    have hu₁_A : u₁ ∈ A := by rw [← h_eq]; exact Finset.mem_insert_self u₁ _
    have hu₁_T : u₁ ∈ T := by rw [← h_eq]; simp
    have hx_ne_v : x ≠ v := fun heq => hx_not_A (heq ▸ hv_A)
    have hx_ne_u₁ : x ≠ u₁ := fun heq => hx_not_A (heq ▸ hu₁_A)
    refine ⟨hu₁_A, hx_not_A, h_ne_12, hx_ne_v, hx_ne_u₁.symm, ?_⟩
    ext y
    constructor
    · intro hy
      by_cases hy_A : y ∈ A
      · have : y ∈ T ∩ A := Finset.mem_inter.mpr ⟨hy, hy_A⟩
        rw [h_eq] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · simp
        · simp
      · have : y ∈ T \ A := Finset.mem_sdiff.mpr ⟨hy, hy_A⟩
        rw [hx_eq] at this
        simp only [Finset.mem_singleton] at this
        simp [this]
    · intro hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hT_v
      · exact hu₁_T
      · exact hx_T

-- ==============================================================================
-- MAIN THEOREM: Bridge externals share apex (THE CRITICAL LEMMA)
-- ==============================================================================

/-- MAIN THEOREM: If T1 is external of A at shared vertex v,
    and T2 is external of B at shared vertex v,
    do they share a common external vertex x (where x not in A and x not in B)?

    This is the make-or-break lemma for proving tau <= 8.

    NOTE: This might be FALSE. The 5-packing argument doesn't directly apply
    because replacing both A and B gives only 4 triangles.

    ARISTOTLE: Try to prove or find counterexample. -/
theorem bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv : v ∈ A ∩ B)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- Extract basic facts
  have hv_A : v ∈ A := Finset.mem_inter.mp hv |>.1
  have hv_B : v ∈ B := Finset.mem_inter.mp hv |>.2

  have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
  have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
  have hA_3 : A.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hA) |>.2
  have hB_3 : B.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hB) |>.2

  -- T1 inter B = {v} (since T1 is external of A, not B)
  have hT₁_B : T₁ ∩ B = {v} := external_inter_nonowner_singleton G M hM A B hA hB hAB v hv_A hv_B T₁ hT₁ hT₁_v hT₁_3

  -- T2 inter A = {v} (since T2 is external of B, not A)
  have hT₂_A : T₂ ∩ A = {v} := external_inter_nonowner_singleton G M hM B A hB hA hAB.symm v hv_B hv_A T₂ hT₂ hT₂_v hT₂_3

  -- Get structure: T1 = {v, a1, x1} with a1 in A, x1 not in A
  obtain ⟨a₁, x₁, ha₁_A, hx₁_not_A, ha₁_ne_v, hx₁_ne_v, ha₁_ne_x₁, hT₁_eq⟩ :=
    external_structure_at_v G M hM A hA v hv_A T₁ hT₁ hT₁_v hT₁_3

  -- Get structure: T2 = {v, b₂, x2} with b₂ in B, x2 not in B
  obtain ⟨b₂, x₂, hb₂_B, hx₂_not_B, hb₂_ne_v, hx₂_ne_v, hb₂_ne_x₂, hT₂_eq⟩ :=
    external_structure_at_v G M hM B hB v hv_B T₂ hT₂ hT₂_v hT₂_3

  -- Key: a1 not in B (since T1 inter B = {v} and a1 != v)
  have ha₁_not_B : a₁ ∉ B := by
    intro ha₁_B
    have : a₁ ∈ T₁ ∩ B := Finset.mem_inter.mpr ⟨by rw [hT₁_eq]; simp, ha₁_B⟩
    rw [hT₁_B] at this
    exact ha₁_ne_v (Finset.mem_singleton.mp this)

  -- Key: b₂ not in A (since T2 inter A = {v} and b₂ != v)
  have hb₂_not_A : b₂ ∉ A := by
    intro hb₂_A
    have : b₂ ∈ T₂ ∩ A := Finset.mem_inter.mpr ⟨by rw [hT₂_eq]; simp, hb₂_A⟩
    rw [hT₂_A] at this
    exact hb₂_ne_v (Finset.mem_singleton.mp this)

  -- THE CRITICAL QUESTION: Does x1 = x2?
  -- If yes, x1 is the common apex (not in A since hx1_not_A, not in B since...)

  -- First check: x1 not in B?
  -- x1 in T1, and T1 inter B = {v}, and x1 != v
  have hx₁_not_B : x₁ ∉ B := by
    intro hx₁_B
    have : x₁ ∈ T₁ ∩ B := Finset.mem_inter.mpr ⟨by rw [hT₁_eq]; simp, hx₁_B⟩
    rw [hT₁_B] at this
    exact hx₁_ne_v (Finset.mem_singleton.mp this)

  -- Similarly: x2 not in A?
  have hx₂_not_A : x₂ ∉ A := by
    intro hx₂_A
    have : x₂ ∈ T₂ ∩ A := Finset.mem_inter.mpr ⟨by rw [hT₂_eq]; simp, hx₂_A⟩
    rw [hT₂_A] at this
    exact hx₂_ne_v (Finset.mem_singleton.mp this)

  -- NOW: If x1 = x2, we have our answer
  -- If x1 != x2, what is T1 inter T2?

  -- T1 = {v, a1, x1}, T2 = {v, b₂, x2}
  -- We know: a1 not in T2 (since a1 in A but T2 inter A = {v} and a1 != v)
  have ha₁_not_T₂ : a₁ ∉ T₂ := by
    intro ha₁_T₂
    rw [hT₂_eq] at ha₁_T₂
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁_T₂
    rcases ha₁_T₂ with rfl | rfl | rfl
    · exact ha₁_ne_v rfl
    · exact ha₁_not_B hb₂_B
    · exact hx₁_not_A (by rw [← ha₁_T₂]; exact ha₁_A)  -- wait, this shows a1 = x2, so x2 in A, contradiction

  -- Similarly b₂ not in T1
  have hb₂_not_T₁ : b₂ ∉ T₁ := by
    intro hb₂_T₁
    rw [hT₁_eq] at hb₂_T₁
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb₂_T₁
    rcases hb₂_T₁ with rfl | rfl | rfl
    · exact hb₂_ne_v rfl
    · exact hb₂_not_A ha₁_A
    · exact hx₂_not_B (by rw [← hb₂_T₁]; exact hb₂_B)

  -- So T1 inter T2 subset {v, x1} inter {v, x2} = {v} union ({x1} inter {x2})
  -- If x1 != x2, then T1 inter T2 = {v}

  -- THIS IS WHERE ARISTOTLE NEEDS TO WORK
  -- The question is: does nu = 4 force x1 = x2?

  sorry

end
