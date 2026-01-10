/-
  slot226_bridge_externals_share_apex.lean

  THE MAKE-OR-BREAK LEMMA FOR τ ≤ 8 (Updated Jan 4, 2026)

  MULTI-AGENT DEBATE CONSENSUS (Jan 4, 2026):
  - τ ≤ 12 is PROVEN (slot139)
  - τ ≤ 8 has ~40% success probability
  - This lemma determines if the vertex-local approach works

  THE KEY QUESTION:
  Given:
    - M = {A, B, C, D} a maximal 4-packing in cycle_4 configuration
    - v is a shared vertex (v ∈ A ∩ B)
    - T₁ is an external of A containing v
    - T₂ is an external of B containing v

  Do T₁ and T₂ share a common external vertex x (where x ∉ A ∧ x ∉ B)?

  If TRUE:  2 edges per shared vertex suffices → τ ≤ 8
  If FALSE: Vertex-local approach blocked → Accept τ ≤ 12

  DIFFICULTY ANALYSIS:
  The standard 5-packing trick from slot182 does NOT directly work because:
  - T₁ is external of A (not B, C, D)
  - T₂ is external of B (not A, C, D)
  - If we try M' = {T₁, T₂, C, D} we get 4 elements, not 5
  - This is NOT a contradiction with ν = 4

  PROOF STRATEGIES TO TRY:
  1. Cross-external edge sharing: Maybe T₁ and T₂ share an edge? This extends slot182.
  2. Composite packing: If x₁ ≠ x₂, can we form a 5-packing using additional triangles?
  3. LP/fractional: If x₁ ≠ x₂, does this allow ν* > 4?
  4. Cycle_4 structure: Use that v is shared by EXACTLY 2 M-elements.

  1 SORRY for Aristotle to fill or find counterexample.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: CORE DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle packing: all elements are triangles and pairwise edge-disjoint -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- A maximal packing: is a packing and every triangle outside shares ≥2 vertices with some M-element -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

/-- Two vertex sets share an edge: ∃ distinct u,v in both sets -/
def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

/-- External triangle of M-element A: triangle in G, not in M, shares edge ONLY with A -/
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

/-- Bridge triangle: shares edges with at least 2 M-elements -/
def isBridgeOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ A B : Finset V, A ∈ M ∧ B ∈ M ∧ A ≠ B ∧ sharesEdgeWith t A ∧ sharesEdgeWith t B

/-- Cycle_4 configuration: 4 M-elements forming a cycle of shared vertices -/
def isCycle4Config (M : Finset (Finset V)) : Prop :=
  M.card = 4 ∧
  ∃ (A B C D : Finset V) (v_ab v_bc v_cd v_da : V),
    M = {A, B, C, D} ∧
    A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
    -- Shared vertices
    v_ab ∈ A ∧ v_ab ∈ B ∧ v_ab ∉ C ∧ v_ab ∉ D ∧
    v_bc ∈ B ∧ v_bc ∈ C ∧ v_bc ∉ D ∧ v_bc ∉ A ∧
    v_cd ∈ C ∧ v_cd ∈ D ∧ v_cd ∉ A ∧ v_cd ∉ B ∧
    v_da ∈ D ∧ v_da ∈ A ∧ v_da ∉ B ∧ v_da ∉ C ∧
    -- All shared vertices are distinct
    v_ab ≠ v_bc ∧ v_bc ≠ v_cd ∧ v_cd ≠ v_da ∧ v_da ≠ v_ab ∧ v_ab ≠ v_cd ∧ v_bc ≠ v_da

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: BASIC SCAFFOLDING LEMMAS (from slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If two sets share an edge (u,v with u≠v), their intersection has ≥2 elements -/
lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  have hu_inter : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu_m⟩
  have hv_inter : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv_m⟩
  exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

/-- Contrapositive: If triangles don't share edge, intersection ≤ 1 -/
lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact h_not_share ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

/-- External of A doesn't share edge with other M-elements → intersection ≤ 1 -/
lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  have ht_3 : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht_ext.1 |>.2
  have hB_3 : B.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hB) |>.2
  exact not_share_implies_one_vertex t B ht_3 hB_3 (ht_ext.2.2.2 B hB hAB.symm)

/-- Key: If no shared edge, triangles intersect in at most 1 vertex -/
lemma edge_disjoint_implies_one_vertex (T₁ T₂ : Finset V)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    (T₁ ∩ T₂).card ≤ 1 := by
  have h_not_share : ¬sharesEdgeWith T₁ T₂ := by
    intro ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
    exact h_edge_disj u v huv hu₁ hv₁ hu₂ hv₂
  exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: 5-PACKING CONSTRUCTION (from slot182)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁, T₂ are edge-disjoint externals of A, then {T₁, T₂, B, C, D} is a 5-packing
    (Proven in slot182) -/
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
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp [hT₁_ne_T₂]
    have h_disj : Disjoint {T₁, T₂} M_minus_A := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · intro heq; exact hT₁_not_MA (heq ▸ hy)
      · intro heq; exact hT₂_not_MA (heq ▸ hy)
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_A_card]
  · constructor
    · intro t ht
      have ht' := Finset.mem_union.mp ht
      rcases ht' with ht_pair | ht_MA
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MA).2
    · intro t₁ ht₁ t₂ ht₂ h_ne
      have ht₁' := Finset.mem_union.mp ht₁
      have ht₂' := Finset.mem_union.mp ht₂
      rcases ht₁' with ht₁_pair | ht₁_MA <;> rcases ht₂' with ht₂_pair | ht₂_MA
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne
          · rw [Finset.mem_singleton] at ht₂_sing; rw [heq₁, ht₂_sing]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂]
            have h := edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
            rw [Finset.inter_comm] at h; exact h
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne
      · have hB_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        have hB_ne_A : t₂ ≠ A := (Finset.mem_erase.mp ht₂_MA).1
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]
          exact external_intersects_other_le_1 G M hM A t₂ hB_M hB_ne_A.symm T₁ hT₁
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          exact external_intersects_other_le_1 G M hM A t₂ hB_M hB_ne_A.symm T₂ hT₂
      · have hB_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have hB_ne_A : t₁ ≠ A := (Finset.mem_erase.mp ht₁_MA).1
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂]
          have h := external_intersects_other_le_1 G M hM A t₁ hB_M hB_ne_A.symm T₁ hT₁
          rw [Finset.inter_comm] at h; exact h
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing]
          have h := external_intersects_other_le_1 G M hM A t₁ hB_M hB_ne_A.symm T₂ hT₂
          rw [Finset.inter_comm] at h; exact h
      · have ht₁_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have ht₂_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        exact hM.1.2 ht₁_M ht₂_M h_ne

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: PROVEN THEOREMS (from slot182 and slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two distinct externals of the SAME M-element must share an edge.
    (Proven in slot182 via 5-packing contradiction) -/
theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  have h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False := by
    intro u v huv hu₁ hv₁ hu₂ hv₂
    exact h_no_edge ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_edge_disj
  have h_bound : M'.card ≤ 4 := hν M' hM'_packing
  omega

/-- Helper: unique external vertex for triangle sharing edge with A -/
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

/-- Externals using DIFFERENT edges of the same A share a common external vertex.
    (Proven in slot224f) -/
theorem different_edges_share_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂)
    (h_diff_edge : T₁ ∩ A ≠ T₂ ∩ A) :
    ∃ x : V, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- Proven in slot224f, included here for completeness
  have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_card : (T₁ ∩ T₂).card ≥ 2 := shares_edge_implies_two_vertices T₁ T₂ h_share
  have hT₁_A : (T₁ ∩ A).card = 2 := by
    have h_ge : (T₁ ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T₁ A hT₁.2.2.1
    have h_le : (T₁ ∩ A).card ≤ 2 := by
      by_contra h_gt
      push_neg at h_gt
      have h_sub : T₁ ⊆ A := by
        have h_inter_sub : T₁ ∩ A ⊆ T₁ := Finset.inter_subset_left
        have h_card_eq : (T₁ ∩ A).card = T₁.card := by
          have h1 : (T₁ ∩ A).card ≤ T₁.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : A ⊆ T₁ := by
        have h_inter_sub : T₁ ∩ A ⊆ A := Finset.inter_subset_right
        have h_card_eq : (T₁ ∩ A).card = A.card := by
          have h1 : (T₁ ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      have h_eq : T₁ = A := Finset.Subset.antisymm h_sub h_sub'
      exact hT₁.2.1 (h_eq ▸ hA)
    linarith
  have hT₂_A : (T₂ ∩ A).card = 2 := by
    have h_ge : (T₂ ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T₂ A hT₂.2.2.1
    have h_le : (T₂ ∩ A).card ≤ 2 := by
      by_contra h_gt
      push_neg at h_gt
      have h_sub : T₂ ⊆ A := by
        have h_inter_sub : T₂ ∩ A ⊆ T₂ := Finset.inter_subset_left
        have h_card_eq : (T₂ ∩ A).card = T₂.card := by
          have h1 : (T₂ ∩ A).card ≤ T₂.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : A ⊆ T₂ := by
        have h_inter_sub : T₂ ∩ A ⊆ A := Finset.inter_subset_right
        have h_card_eq : (T₂ ∩ A).card = A.card := by
          have h1 : (T₂ ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      have h_eq : T₂ = A := Finset.Subset.antisymm h_sub h_sub'
      exact hT₂.2.1 (h_eq ▸ hA)
    linarith
  obtain ⟨x₁, ⟨hx₁_T₁, hx₁_not_A⟩, hx₁_unique⟩ := external_has_unique_outside_vertex T₁ A hT₁_3 hT₁_A
  obtain ⟨x₂, ⟨hx₂_T₂, hx₂_not_A⟩, hx₂_unique⟩ := external_has_unique_outside_vertex T₂ A hT₂_3 hT₂_A
  have h_A_edges_share_one : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card = 1 := by
    have h_sub1 : T₁ ∩ A ⊆ A := Finset.inter_subset_right
    have h_sub2 : T₂ ∩ A ⊆ A := Finset.inter_subset_right
    have h_union : (T₁ ∩ A) ∪ (T₂ ∩ A) ⊆ A := Finset.union_subset h_sub1 h_sub2
    have h_union_card : ((T₁ ∩ A) ∪ (T₂ ∩ A)).card ≤ 3 :=
      le_trans (Finset.card_le_card h_union) (le_of_eq hA_3)
    have h_inclusion := Finset.card_union_add_card_inter (T₁ ∩ A) (T₂ ∩ A)
    have h_inter_le : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card < 2 := by
      by_contra h_ge_2
      push_neg at h_ge_2
      have h_eq : T₁ ∩ A = T₂ ∩ A := by
        have h1 : (T₁ ∩ A) ∩ (T₂ ∩ A) ⊆ T₁ ∩ A := Finset.inter_subset_left
        have h2 : (T₁ ∩ A) ∩ (T₂ ∩ A) ⊆ T₂ ∩ A := Finset.inter_subset_right
        have hcard1 : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card = (T₁ ∩ A).card := by
          have := Finset.card_le_card h1
          linarith
        have hcard2 : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card = (T₂ ∩ A).card := by
          have := Finset.card_le_card h2
          linarith
        have heq1 : (T₁ ∩ A) ∩ (T₂ ∩ A) = T₁ ∩ A := Finset.eq_of_subset_of_card_le h1 (le_of_eq hcard1.symm)
        have heq2 : (T₁ ∩ A) ∩ (T₂ ∩ A) = T₂ ∩ A := Finset.eq_of_subset_of_card_le h2 (le_of_eq hcard2.symm)
        exact heq1.symm.trans heq2
      exact h_diff_edge h_eq
    linarith
  have h_x_eq : x₁ = x₂ := by
    by_contra h_ne_x
    have h_subset : T₁ ∩ T₂ ⊆ ((T₁ ∩ A) ∩ (T₂ ∩ A)) ∪ ({x₁} ∩ {x₂}) := by
      intro v hv
      have hv₁ : v ∈ T₁ := Finset.mem_inter.mp hv |>.1
      have hv₂ : v ∈ T₂ := Finset.mem_inter.mp hv |>.2
      by_cases hv_A : v ∈ A
      · apply Finset.mem_union.mpr
        left
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hv₁, hv_A⟩,
                                    Finset.mem_inter.mpr ⟨hv₂, hv_A⟩⟩
      · have hv_x₁ : v = x₁ := hx₁_unique v ⟨hv₁, hv_A⟩
        have hv_x₂ : v = x₂ := hx₂_unique v ⟨hv₂, hv_A⟩
        exact absurd (hv_x₁.symm.trans hv_x₂) h_ne_x
    have h_x_inter : ({x₁} ∩ {x₂} : Finset V) = ∅ := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.not_mem_empty, iff_false]
      intro ⟨hv₁, hv₂⟩
      exact h_ne_x (hv₁.symm.trans hv₂)
    rw [h_x_inter, Finset.union_empty] at h_subset
    have h_bound : (T₁ ∩ T₂).card ≤ ((T₁ ∩ A) ∩ (T₂ ∩ A)).card := Finset.card_le_card h_subset
    linarith
  use x₁
  exact ⟨hx₁_not_A, hx₁_T₁, h_x_eq ▸ hx₂_T₂⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: NEW HELPER LEMMAS FOR CROSS-ELEMENT EXTERNALS
-- ══════════════════════════════════════════════════════════════════════════════

/-- External of A shares exactly 2 vertices with A (the edge it borrows) -/
lemma external_intersection_with_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_3 : T.card = 3) :
    (T ∩ A).card = 2 := by
  have h_ge : (T ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T A hT.2.2.1
  have h_le : (T ∩ A).card ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h_sub : T ⊆ A := by
      have h_inter_sub : T ∩ A ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ A).card = T.card := by
        have h1 : (T ∩ A).card ≤ T.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.2
    have h_sub' : A ⊆ T := by
      have h_inter_sub : T ∩ A ⊆ A := Finset.inter_subset_right
      have h_card_eq : (T ∩ A).card = A.card := by
        have h1 : (T ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.1
    have h_eq : T = A := Finset.Subset.antisymm h_sub h_sub'
    exact hT.2.1 (h_eq ▸ hA)
  linarith

/-- External of A containing shared vertex v uses edge incident to v -/
lemma external_at_shared_uses_incident_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (hA_3 : A.card = 3) (hB_3 : B.card = 3)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_3 : T.card = 3) (hT_v : v ∈ T) :
    v ∈ T ∩ A := by
  exact Finset.mem_inter.mpr ⟨hT_v, hv_A⟩

/-- T₁ (external of A) cannot share edge with B (by definition of external) -/
lemma external_A_not_share_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (T : Finset V) (hT : isExternalOf G M A T) :
    ¬sharesEdgeWith T B := by
  exact hT.2.2.2 B hB hAB.symm

/-- If T₁ contains v and is external of A, then T₁ ∩ B has ≤ 1 vertex -/
lemma external_A_intersect_B_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_3 : T.card = 3) (hB_3 : B.card = 3) :
    (T ∩ B).card ≤ 1 := by
  have h_not_share := external_A_not_share_B G M A B hA hB hAB T hT
  exact not_share_implies_one_vertex T B hT_3 hB_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: POTENTIAL 4-PACKING STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- When we replace A with T₁ and B with T₂, we get a 4-element set (NOT 5-packing)
    This is why the direct 5-packing approach doesn't work. -/
lemma four_element_replacement (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂) :
    let M' := (M.erase A).erase B ∪ {T₁, T₂}
    M'.card = 4 := by
  simp only
  have h_not_M_T₁ : T₁ ∉ M := hT₁.2.1
  have h_not_M_T₂ : T₂ ∉ M := hT₂.2.1
  have h_erase_A : (M.erase A).card = 3 := by rw [Finset.card_erase_of_mem hA]; omega
  have hB_in_erase : B ∈ M.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have h_erase_AB : ((M.erase A).erase B).card = 2 := by
    rw [Finset.card_erase_of_mem hB_in_erase]; omega
  have h_pair : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_singleton]; simp [hT₁_ne_T₂]
  have h_T₁_not_erase : T₁ ∉ (M.erase A).erase B := fun h =>
    h_not_M_T₁ ((Finset.mem_erase.mp h).2 |> Finset.mem_erase.mp |>.2)
  have h_T₂_not_erase : T₂ ∉ (M.erase A).erase B := fun h =>
    h_not_M_T₂ ((Finset.mem_erase.mp h).2 |> Finset.mem_erase.mp |>.2)
  have h_disj : Disjoint ((M.erase A).erase B) {T₁, T₂} := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · intro heq; exact h_T₁_not_erase (heq ▸ hx)
    · intro heq; exact h_T₂_not_erase (heq ▸ hx)
  rw [Finset.card_union_of_disjoint h_disj.symm, h_erase_AB, h_pair]

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 7: CROSS-EXTERNAL PACKING ANALYSIS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key observation: If T₁ (external of A) and T₂ (external of B) with A ≠ B both
    contain v (where v ∈ A ∩ B), then replacing A, B with T₁, T₂ gives a 4-packing
    (not 5-packing). To get a 5-packing contradiction, we need ANOTHER triangle.

    STRATEGY: Use the external vertex.
    If T₁ = {v, a', x₁} and T₂ = {v, b', x₂} with x₁ ≠ x₂ and x₁, x₂ external to M,
    we might be able to construct a 5th triangle or show a structural contradiction. -/

/-- Potential 5-packing from different external vertices.
    This lemma is speculative and may help or may not be true. -/
lemma cross_externals_packing_analysis (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V)
    (hA : A ∈ M) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hA_3 : A.card = 3) (hB_3 : B.card = 3)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B) (hv_not_C : v ∉ C) (hv_not_D : v ∉ D)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    -- x₁ is the external vertex of T₁ (the vertex not in A)
    (x₁ : V) (hx₁_T₁ : x₁ ∈ T₁) (hx₁_not_A : x₁ ∉ A) (hx₁_not_v : x₁ ≠ v)
    -- x₂ is the external vertex of T₂ (the vertex not in B)
    (x₂ : V) (hx₂_T₂ : x₂ ∈ T₂) (hx₂_not_B : x₂ ∉ B) (hx₂_not_v : x₂ ≠ v)
    -- Suppose x₁ ≠ x₂ (this is what we want to contradict)
    (hx₁_ne_x₂ : x₁ ≠ x₂) :
    -- Then we should be able to derive a contradiction...
    -- The difficulty is that M' = {T₁, T₂, C, D} is only a 4-packing
    -- We need additional structure to get a contradiction
    True := by
  -- This is a placeholder for the analysis
  -- The full proof requires careful case analysis on graph structure
  trivial

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 8: THE MAIN THEOREM (1 SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/--
  Bridge Externals Share Apex Lemma

  Given:
  - M = {A, B, C, D} a maximal 4-packing in cycle_4 configuration
  - v is a shared vertex (v ∈ A ∩ B)
  - T₁ is an external of A containing v
  - T₂ is an external of B containing v

  Claim: T₁ and T₂ share a common external vertex x (where x ∉ A and x ∉ B)

  If TRUE:
  - At each shared vertex, all externals share a common apex x
  - Cover: {v, x} covers all externals at v (2 edges per shared vertex)
  - Total: 4 shared vertices × 2 = 8 edges → τ ≤ 8

  If FALSE (Aristotle finds counterexample):
  - Pattern 6 is confirmed: externals of different M-elements can have different apexes
  - The vertex-local 2-edge approach is blocked
  - Accept τ ≤ 12 or find alternative approach

  PROOF STRATEGIES FOR ARISTOTLE:

  Strategy 1 - Cross-M edge sharing:
  Show that T₁ and T₂ must share an edge (extending slot182 across M-elements).
  Difficulty: slot182 uses 5-packing, but here we only get 4-packing.

  Strategy 2 - Use cycle structure:
  In cycle_4: A∩B = {v_ab}, B∩C = {v_bc}, C∩D = {v_cd}, D∩A = {v_da}
  T₁ uses edge {v, a'} from A (where a' is a non-shared vertex of A)
  T₂ uses edge {v, b'} from B (where b' is a non-shared vertex of B)
  If x₁ ≠ x₂, analyze the implications...

  Strategy 3 - Counting argument:
  Each M-element has 3 edges. At each shared vertex, 2 edges are "incident" to v.
  Count how many externals can exist with different apexes.

  Strategy 4 - LP relaxation:
  If x₁ ≠ x₂, construct fractional packing with ν* > 4.
-/
theorem bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (hA_3 : A.card = 3) (hB_3 : B.card = 3)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)  -- v is shared vertex
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂)  -- both externals contain v
    (hT₁_ne_T₂ : T₁ ≠ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  /-
    PROOF SKETCH for Aristotle:

    1. Let T₁ = {v, a', x₁} where {v, a'} is an edge of A and x₁ ∉ A
    2. Let T₂ = {v, b', x₂} where {v, b'} is an edge of B and x₂ ∉ B

    Key observations:
    - T₁ ∩ A = {v, a'} (card 2)
    - T₂ ∩ B = {v, b'} (card 2)
    - T₁ ∩ B has card ≤ 1 (since T₁ is external of A, doesn't share edge with B)
    - T₂ ∩ A has card ≤ 1 (since T₂ is external of B, doesn't share edge with A)

    Since v ∈ T₁ ∩ B and v ∈ T₂ ∩ A, we have:
    - T₁ ∩ B = {v}
    - T₂ ∩ A = {v}

    Therefore:
    - a' ∉ B (otherwise |T₁ ∩ B| ≥ 2)
    - b' ∉ A (otherwise |T₂ ∩ A| ≥ 2)

    Now suppose x₁ ≠ x₂.
    Consider T₁ ∩ T₂.

    T₁ ∩ T₂ must include v (since v ∈ T₁ and v ∈ T₂).

    Can T₁ ∩ T₂ include a'?
    - a' ∈ T₁ and a' ∉ B
    - If a' ∈ T₂, then T₂ = {v, b', a'} or {v, b', x₂}
    - If a' = b', then a' ∈ A ∩ B = {v}, but a' ≠ v (since a' is the other vertex)
    - If a' = x₂, then x₂ = a' ∈ A, but x₂ ∉ B and we need to check...

    This is getting complex. Let Aristotle work through the cases.
  -/
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 9: COROLLARIES (if main theorem holds)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If bridge_externals_share_apex holds, then at each shared vertex v:
    The edge {v, x} (where x is the common apex) covers all externals of both A and B at v. -/
theorem two_edges_cover_at_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (hA_3 : A.card = 3) (hB_3 : B.card = 3)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (h_apex : ∀ T₁ T₂ : Finset V,
      isExternalOf G M A T₁ → isExternalOf G M B T₂ →
      T₁.card = 3 → T₂.card = 3 →
      v ∈ T₁ → v ∈ T₂ → T₁ ≠ T₂ →
      ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂) :
    -- There exist 2 edges that cover all externals at v
    ∃ e₁ e₂ : Sym2 V, ∀ T : Finset V,
      T ∈ G.cliqueFinset 3 → T ∉ M → v ∈ T →
      sharesEdgeWith T A ∨ sharesEdgeWith T B →
      (∃ uv ∈ e₁.toFinset, uv ∈ T) ∨ (∃ uv ∈ e₂.toFinset, uv ∈ T) := by
  -- This follows from the apex lemma but requires careful analysis
  sorry

/-- Ultimate goal: τ ≤ 8 for cycle_4 configuration -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hCycle4 : isCycle4Config M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_apex : ∀ A B v T₁ T₂, A ∈ M → B ∈ M → A ≠ B → A.card = 3 → B.card = 3 →
      v ∈ A → v ∈ B → isExternalOf G M A T₁ → isExternalOf G M B T₂ →
      T₁.card = 3 → T₂.card = 3 → v ∈ T₁ → v ∈ T₂ → T₁ ≠ T₂ →
      ∃ x, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by
  -- If bridge_externals_share_apex holds for all pairs, we can construct
  -- an 8-edge cover: 4 M-edges + 4 edges {v_ij, x_ij} at each shared vertex
  sorry

end
