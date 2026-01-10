/-
  slot301: Fan Apex Inside A

  GOAL: Prove that the common vertex shared by all A-externals is INSIDE A.

  CONTEXT:
  - From slot182 (PROVEN): Two A-externals share an edge
  - From slot224f (PROVEN): A-externals using different A-edges share external vertex x ∉ A

  KEY INSIGHT: The "external vertex" from slot224f is actually constrained.
  For PATH_4, A = {v1, a1, a2} where v1 is the spine vertex.

  CLAIM: All A-externals share a common vertex that is INSIDE A (not outside).

  PROOF SKETCH:
  1. Any two A-externals T₁, T₂ share an edge {u,v} (by slot182)
  2. This shared edge must contain at least one vertex from A
     (since T₁ shares edge with A, and T₂ shares edge with A)
  3. Therefore the common vertex is in A

  This allows us to cover ALL A-externals with just 2 edges incident to this vertex!

  MULTI-AGENT VERIFIED (Jan 8, 2026):
  - Strategist C proposed this approach
  - Critic A validated the edge overlap reasoning
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot182)
-- ══════════════════════════════════════════════════════════════════════════════

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
-- SCAFFOLDING LEMMAS (from slot182, slot224f)
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

-- slot182: Two externals share an edge
lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  -- If T₁, T₂ don't share an edge, they're edge-disjoint
  -- Then {T₁, T₂} ∪ (M \ {A}) is a 5-packing, contradicting ν = 4
  have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
  have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
  have h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False :=
    fun u v huv hu₁ hv₁ hu₂ hv₂ => h_no_edge ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
  -- Construct M' = {T₁, T₂} ∪ (M \ {A})
  let M_minus_A := M.erase A
  let M' := {T₁, T₂} ∪ M_minus_A
  have hM'_card : M'.card = 5 := by
    have hT₁_not_M : T₁ ∉ M := hT₁.2.1
    have hT₂_not_M : T₂ ∉ M := hT₂.2.1
    have hM_minus_A_card : M_minus_A.card = 3 := by rw [Finset.card_erase_of_mem hA]; omega
    have hT₁_not_MA : T₁ ∉ M_minus_A := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MA : T₂ ∉ M_minus_A := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem]; simp [h_ne]; simp [h_ne]
    have h_disj : Disjoint {T₁, T₂} M_minus_A := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact fun h => hT₁_not_MA (h ▸ hy);
                                    exact fun h => hT₂_not_MA (h ▸ hy)]
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_A_card]
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht_pair | ht_MA
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MA).2
    · intro t₁ ht₁ t₂ ht₂ h_ne'
      rcases Finset.mem_union.mp ht₁ with ht₁_pair | ht₁_MA <;>
      rcases Finset.mem_union.mp ht₂ with ht₂_pair | ht₂_MA
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
      · have hB_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        have hB_ne_A : t₂ ≠ A := (Finset.mem_erase.mp ht₂_MA).1
        have hB_3 : t₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hB_M) |>.2
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]
          have h_not_share := hT₁.2.2.2 t₂ hB_M hB_ne_A
          exact not_share_implies_one_vertex T₁ t₂ hT₁_3 hB_3 h_not_share
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          have h_not_share := hT₂.2.2.2 t₂ hB_M hB_ne_A
          exact not_share_implies_one_vertex T₂ t₂ hT₂_3 hB_3 h_not_share
      · have hB_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have hB_ne_A : t₁ ≠ A := (Finset.mem_erase.mp ht₁_MA).1
        have hB_3 : t₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hB_M) |>.2
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂, Finset.inter_comm]
          have h_not_share := hT₁.2.2.2 t₁ hB_M hB_ne_A
          exact not_share_implies_one_vertex T₁ t₁ hT₁_3 hB_3 h_not_share
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing, Finset.inter_comm]
          have h_not_share := hT₂.2.2.2 t₁ hB_M hB_ne_A
          exact not_share_implies_one_vertex T₂ t₁ hT₂_3 hB_3 h_not_share
      · exact hM.1.2 (Finset.mem_erase.mp ht₁_MA).2 (Finset.mem_erase.mp ht₂_MA).2 h_ne'
  have h_bound := hν M' hM'_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Shared edge contains A-vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- The edge shared by two A-externals must contain a vertex from A.

PROOF SKETCH:
1. T₁ shares edge {u₁, v₁} with A, so u₁, v₁ ∈ A
2. T₂ shares edge {u₂, v₂} with A, so u₂, v₂ ∈ A
3. T₁ ∩ T₂ has ≥ 2 vertices (they share an edge)
4. T₁ ∩ A and T₂ ∩ A each have exactly 2 vertices
5. Since T₁ and T₂ are triangles with |T₁| = |T₂| = 3 and |T_i ∩ A| = 2,
   each T_i has exactly 1 vertex outside A
6. The shared edge {x, y} ∈ T₁ ∩ T₂ must have x ∈ A or y ∈ A
   (otherwise T₁ \ A and T₂ \ A would each have ≥ 2 elements)
-/
theorem shared_edge_contains_A_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ T₁ ∩ T₂, x ∈ A := by
  -- Get the shared edge
  have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_card : (T₁ ∩ T₂).card ≥ 2 := shares_edge_implies_two_vertices T₁ T₂ h_share

  -- T₁ ∩ A and T₂ ∩ A each have exactly 2 vertices
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

  -- Each triangle has exactly 1 vertex outside A
  have h_T₁_outside : (T₁ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₁ A
    omega

  have h_T₂_outside : (T₂ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₂ A
    omega

  -- Now prove some vertex in T₁ ∩ T₂ is in A
  -- Suppose not: all of T₁ ∩ T₂ is outside A
  by_contra h_none_in_A
  push_neg at h_none_in_A

  -- Then T₁ ∩ T₂ ⊆ T₁ \ A
  have h_sub_out₁ : T₁ ∩ T₂ ⊆ T₁ \ A := by
    intro x hx
    have hx₁ : x ∈ T₁ := Finset.mem_inter.mp hx |>.1
    have hx_not_A : x ∉ A := h_none_in_A x hx
    exact Finset.mem_sdiff.mpr ⟨hx₁, hx_not_A⟩

  -- But |T₁ ∩ T₂| ≥ 2 and |T₁ \ A| = 1, contradiction!
  have h_card_bound : (T₁ ∩ T₂).card ≤ (T₁ \ A).card := Finset.card_le_card h_sub_out₁
  omega

end
