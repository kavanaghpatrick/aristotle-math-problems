/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 132fbf2a-84e5-4fef-b2e6-0eb93e9c5d7e
-/

/-
  slot303: Middle Element Fan Apex Inside B

  GOAL: Prove that B-externals share a vertex that is INSIDE B.

  CONTEXT:
  - From slot301 (PROVEN): For endpoints A, D, the shared edge of two externals
    contains a vertex from the element itself.
  - This file extends that result to MIDDLE elements B and C.

  PATH_4 STRUCTURE:
  - A = {v1, a1, a2} (endpoint)
  - B = {v1, v2, b}  (middle - shares v1 with A, v2 with C)
  - C = {v2, v3, c}  (middle - shares v2 with B, v3 with D)
  - D = {v3, d1, d2} (endpoint)

  KEY INSIGHT: Middle elements have TWO shared vertices (v1 and v2 for B).
  B-externals must share an edge with B = {v1, v2, b}.
  The edge types are: {v1,v2}, {v1,b}, {v2,b}

  CLAIM: All B-externals share a common vertex that is in B.

  PROOF SKETCH:
  1. Any two B-externals T₁, T₂ share an edge (by two_externals_share_edge)
  2. Each T_i shares an edge with B, so (T_i ∩ B).card = 2
  3. Each T_i has exactly 1 vertex outside B
  4. If T₁ ∩ T₂ were entirely outside B, then |T₁ ∩ T₂| ≤ 1
  5. But |T₁ ∩ T₂| ≥ 2 (they share an edge) → Contradiction!
  6. Therefore some vertex in T₁ ∩ T₂ is in B

  This is the SAME proof as slot301, just applied to B instead of A!
-/

import Mathlib


set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING (from slot301)
-- ══════════════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu_t, hu_m⟩,
                                 v, Finset.mem_inter.mpr ⟨hv_t, hv_m⟩, huv⟩

lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact h_not_share ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

lemma edge_disjoint_implies_one_vertex (T₁ T₂ : Finset V)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    (T₁ ∩ T₂).card ≤ 1 := by
  have h_not_share : ¬sharesEdgeWith T₁ T₂ := fun ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩ =>
    h_edge_disj u v huv hu₁ hv₁ hu₂ hv₂
  exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_not_share

-- Two externals share an edge (from slot182)
lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (B : Finset V) (hB : B ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M B T₁) (hT₂ : isExternalOf G M B T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
  have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
  have h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False :=
    fun u v huv hu₁ hv₁ hu₂ hv₂ => h_no_edge ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
  let M_minus_B := M.erase B
  let M' := {T₁, T₂} ∪ M_minus_B
  have hM'_card : M'.card = 5 := by
    have hT₁_not_M : T₁ ∉ M := hT₁.2.1
    have hT₂_not_M : T₂ ∉ M := hT₂.2.1
    have hM_minus_B_card : M_minus_B.card = 3 := by rw [Finset.card_erase_of_mem hB]; omega
    have hT₁_not_MB : T₁ ∉ M_minus_B := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MB : T₂ ∉ M_minus_B := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem]; simp [h_ne]; simp [h_ne]
    have h_disj : Disjoint {T₁, T₂} M_minus_B := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact fun h => hT₁_not_MB (h ▸ hy);
                                    exact fun h => hT₂_not_MB (h ▸ hy)]
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_B_card]
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht_pair | ht_MB
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MB).2
    · intro t₁ ht₁ t₂ ht₂ h_ne'
      rcases Finset.mem_union.mp ht₁ with ht₁_pair | ht₁_MB <;>
      rcases Finset.mem_union.mp ht₂ with ht₂_pair | ht₂_MB
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne'
          · rw [Finset.mem_singleton] at ht₂_sing; rw [heq₁, ht₂_sing]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂, Finset.inter_comm]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne'
      · have hX_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MB).2
        have hX_ne_B : t₂ ≠ B := (Finset.mem_erase.mp ht₂_MB).1
        have hX_3 : t₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hX_M) |>.2
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]
          have h_not_share := hT₁.2.2.2 t₂ hX_M hX_ne_B
          exact not_share_implies_one_vertex T₁ t₂ hT₁_3 hX_3 h_not_share
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          have h_not_share := hT₂.2.2.2 t₂ hX_M hX_ne_B
          exact not_share_implies_one_vertex T₂ t₂ hT₂_3 hX_3 h_not_share
      · have hX_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MB).2
        have hX_ne_B : t₁ ≠ B := (Finset.mem_erase.mp ht₁_MB).1
        have hX_3 : t₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hX_M) |>.2
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂, Finset.inter_comm]
          have h_not_share := hT₁.2.2.2 t₁ hX_M hX_ne_B
          exact not_share_implies_one_vertex T₁ t₁ hT₁_3 hX_3 h_not_share
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing, Finset.inter_comm]
          have h_not_share := hT₂.2.2.2 t₁ hX_M hX_ne_B
          exact not_share_implies_one_vertex T₂ t₁ hT₂_3 hX_3 h_not_share
      · exact hM.1.2 (Finset.mem_erase.mp ht₁_MB).2 (Finset.mem_erase.mp ht₂_MB).2 h_ne'
  have h_bound := hν M' hM'_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Middle element fan apex inside B
-- ══════════════════════════════════════════════════════════════════════════════

/-- The edge shared by two B-externals contains a vertex from B.

This is the same result as slot301, but for middle element B instead of endpoint A.
The proof is identical: triangles sharing an edge with B have 2 vertices in B,
so they have 1 vertex outside B, and the shared edge can't fit entirely outside.
-/
theorem middle_fan_apex_in_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (B : Finset V) (hB : B ∈ M) (hB_3 : B.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M B T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ T₁ ∩ T₂, x ∈ B := by
  -- Get the shared edge
  have h_share := two_externals_share_edge G M hM hM_card hν B hB T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_card : (T₁ ∩ T₂).card ≥ 2 := shares_edge_implies_two_vertices T₁ T₂ h_share

  -- T₁ ∩ B and T₂ ∩ B each have exactly 2 vertices
  have hT₁_B : (T₁ ∩ B).card = 2 := by
    have h_ge : (T₁ ∩ B).card ≥ 2 := shares_edge_implies_two_vertices T₁ B hT₁.2.2.1
    have h_le : (T₁ ∩ B).card ≤ 2 := by
      by_contra h_gt
      push_neg at h_gt
      have h_sub : T₁ ⊆ B := by
        have h_inter_sub : T₁ ∩ B ⊆ T₁ := Finset.inter_subset_left
        have h_card_eq : (T₁ ∩ B).card = T₁.card := by
          have h1 : (T₁ ∩ B).card ≤ T₁.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : B ⊆ T₁ := by
        have h_inter_sub : T₁ ∩ B ⊆ B := Finset.inter_subset_right
        have h_card_eq : (T₁ ∩ B).card = B.card := by
          have h1 : (T₁ ∩ B).card ≤ B.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      have h_eq : T₁ = B := Finset.Subset.antisymm h_sub h_sub'
      exact hT₁.2.1 (h_eq ▸ hB)
    linarith

  have hT₂_B : (T₂ ∩ B).card = 2 := by
    have h_ge : (T₂ ∩ B).card ≥ 2 := shares_edge_implies_two_vertices T₂ B hT₂.2.2.1
    have h_le : (T₂ ∩ B).card ≤ 2 := by
      by_contra h_gt
      push_neg at h_gt
      have h_sub : T₂ ⊆ B := by
        have h_inter_sub : T₂ ∩ B ⊆ T₂ := Finset.inter_subset_left
        have h_card_eq : (T₂ ∩ B).card = T₂.card := by
          have h1 : (T₂ ∩ B).card ≤ T₂.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : B ⊆ T₂ := by
        have h_inter_sub : T₂ ∩ B ⊆ B := Finset.inter_subset_right
        have h_card_eq : (T₂ ∩ B).card = B.card := by
          have h1 : (T₂ ∩ B).card ≤ B.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      have h_eq : T₂ = B := Finset.Subset.antisymm h_sub h_sub'
      exact hT₂.2.1 (h_eq ▸ hB)
    linarith

  -- Each triangle has exactly 1 vertex outside B
  have h_T₁_outside : (T₁ \ B).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₁ B
    omega

  have h_T₂_outside : (T₂ \ B).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₂ B
    omega

  -- Now prove some vertex in T₁ ∩ T₂ is in B
  by_contra h_none_in_B
  push_neg at h_none_in_B

  -- Then T₁ ∩ T₂ ⊆ T₁ \ B
  have h_sub_out₁ : T₁ ∩ T₂ ⊆ T₁ \ B := by
    intro x hx
    have hx₁ : x ∈ T₁ := Finset.mem_inter.mp hx |>.1
    have hx_not_B : x ∉ B := h_none_in_B x hx
    exact Finset.mem_sdiff.mpr ⟨hx₁, hx_not_B⟩

  -- But |T₁ ∩ T₂| ≥ 2 and |T₁ \ B| = 1, contradiction!
  have h_card_bound : (T₁ ∩ T₂).card ≤ (T₁ \ B).card := Finset.card_le_card h_sub_out₁
  omega

end