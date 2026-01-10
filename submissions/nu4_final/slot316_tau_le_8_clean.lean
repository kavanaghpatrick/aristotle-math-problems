/-
  slot316: τ ≤ 8 for ν = 4 - Clean version

  Key scaffolding for Aristotle with minimal API surface.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
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
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangle in cliqueFinset 3 has card 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  have := SimpleGraph.mem_cliqueFinset_iff.mp hT
  exact this.2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: sharesEdgeWith ↔ intersection ≥ 2
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External has exactly one vertex outside X
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_has_one_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T \ X).card = 1 := by
  have hT_card : T.card = 3 := triangle_card_three G T hT.1
  have h_share : sharesEdgeWith T X := hT.2.2.1
  have h_inter_ge : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
  have h_inter_le : (T ∩ X).card ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by
        have h1 : (T ∩ X).card ≤ T.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by
        have h1 : (T ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.1
    have h_eq : T = X := Finset.Subset.antisymm h_sub h_sub'
    exact hT.2.1 (h_eq ▸ hX_in_M)
  have h_inter : (T ∩ X).card = 2 := by omega
  have := Finset.card_sdiff_add_card_inter T X
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Two externals share edge (5-packing argument)
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_share
  -- If T₁ and T₂ don't share an edge, we can form a 5-packing
  -- Construct M' = {T₁, T₂} ∪ (M \ {X})
  let M' := insert T₁ (insert T₂ (M.erase X))
  have hM'_card : M'.card = 5 := by
    have h1 : T₁ ∉ M := hT₁.2.1
    have h2 : T₂ ∉ M := hT₂.2.1
    have h3 : (M.erase X).card = 3 := by rw [Finset.card_erase_of_mem hX]; omega
    have h4 : T₁ ∉ insert T₂ (M.erase X) := by
      simp only [Finset.mem_insert, Finset.mem_erase]
      intro h
      rcases h with rfl | ⟨_, h⟩
      · exact h_ne rfl
      · exact h1 h
    have h5 : T₂ ∉ M.erase X := by
      simp only [Finset.mem_erase]
      intro ⟨_, h⟩
      exact h2 h
    simp only [M', Finset.card_insert_of_not_mem h4, Finset.card_insert_of_not_mem h5, h3]
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · intro t ht
      simp only [M', Finset.mem_insert, Finset.mem_erase] at ht
      rcases ht with rfl | rfl | ⟨_, ht⟩
      · exact hT₁.1
      · exact hT₂.1
      · exact hM.1.1 ht
    · intro t₁ ht₁ t₂ ht₂ hne
      simp only [M', Finset.mem_insert, Finset.mem_erase] at ht₁ ht₂
      -- Case analysis on t₁ and t₂
      rcases ht₁ with rfl | rfl | ⟨hne₁, ht₁⟩ <;>
      rcases ht₂ with rfl | rfl | ⟨hne₂, ht₂⟩
      · exact absurd rfl hne
      · -- T₁ and T₂ don't share edge
        have := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂
        simp only [not_le] at h_no_share
        push_neg at this
        exact Nat.lt_succ_iff.mp (this.mp h_no_share)
      · -- T₁ and some Y ∈ M \ {X}
        have hY_ne_X : t₂ ≠ X := hne₂
        have := hT₁.2.2.2 t₂ ht₂ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₁ t₂
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · rw [Finset.inter_comm]
        have := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂
        simp only [not_le] at h_no_share
        push_neg at this
        exact Nat.lt_succ_iff.mp (this.mp h_no_share)
      · exact absurd rfl hne
      · have hY_ne_X : t₂ ≠ X := hne₂
        have := hT₂.2.2.2 t₂ ht₂ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₂ t₂
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · rw [Finset.inter_comm]
        have hY_ne_X : t₁ ≠ X := hne₁
        have := hT₁.2.2.2 t₁ ht₁ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₁ t₁
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · rw [Finset.inter_comm]
        have hY_ne_X : t₁ ≠ X := hne₁
        have := hT₂.2.2.2 t₁ ht₁ hY_ne_X
        have h := sharesEdgeWith_iff_card_inter_ge_two T₂ t₁
        push_neg at this h
        exact Nat.lt_succ_iff.mp (h.mp this)
      · exact hM.1.2 ht₁ ht₂ hne
  have := hν M' hM'_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Externals with different outside vertices share same X-edge
-- ══════════════════════════════════════════════════════════════════════════════

lemma externals_disjoint_outside_implies_same_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    T₁ ∩ X = T₂ ∩ X := by
  have hT₁_card : T₁.card = 3 := triangle_card_three G T₁ hT₁.1
  have hT₂_card : T₂.card = 3 := triangle_card_three G T₂ hT₂.1
  have h_out₁ : (T₁ \ X).card = 1 := external_has_one_outside G M X hX hX_3 T₁ hT₁
  have h_out₂ : (T₂ \ X).card = 1 := external_has_one_outside G M X hX hX_3 T₂ hT₂
  have h_inter_card₁ : (T₁ ∩ X).card = 2 := by
    have := Finset.card_sdiff_add_card_inter T₁ X; omega
  have h_inter_card₂ : (T₂ ∩ X).card = 2 := by
    have := Finset.card_sdiff_add_card_inter T₂ X; omega
  have hT₁_ne_T₂ : T₁ ≠ T₂ := by
    intro h_eq
    rw [h_eq] at h_diff
    exact h_diff rfl
  have h_share : sharesEdgeWith T₁ T₂ := two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ hT₁_ne_T₂
  have h_T₁T₂ : (T₁ ∩ T₂).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂ |>.mp h_share
  -- The shared edge of T₁ and T₂ must be in X (since their outside vertices differ)
  have h_disj : (T₁ \ X) ∩ (T₂ \ X) = ∅ := by
    obtain ⟨v₁, hv₁⟩ := Finset.card_eq_one.mp h_out₁
    obtain ⟨v₂, hv₂⟩ := Finset.card_eq_one.mp h_out₂
    have hne : v₁ ≠ v₂ := by
      intro h_eq
      rw [h_eq] at hv₁
      exact h_diff (hv₁.trans hv₂.symm)
    rw [hv₁, hv₂]
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.not_mem_empty, iff_false]
    intro ⟨h1, h2⟩
    exact hne (h1.trans h2.symm)
  -- T₁ ∩ T₂ ⊆ X (since outside parts are disjoint)
  have h_in_X : T₁ ∩ T₂ ⊆ X := by
    intro x hx
    simp only [Finset.mem_inter] at hx
    by_contra hx_not_X
    have hx_out₁ : x ∈ T₁ \ X := Finset.mem_sdiff.mpr ⟨hx.1, hx_not_X⟩
    have hx_out₂ : x ∈ T₂ \ X := Finset.mem_sdiff.mpr ⟨hx.2, hx_not_X⟩
    have : x ∈ (T₁ \ X) ∩ (T₂ \ X) := Finset.mem_inter.mpr ⟨hx_out₁, hx_out₂⟩
    rw [h_disj] at this
    exact Finset.not_mem_empty x this
  -- So T₁ ∩ T₂ ⊆ T₁ ∩ X and T₁ ∩ T₂ ⊆ T₂ ∩ X
  have h_sub₁ : T₁ ∩ T₂ ⊆ T₁ ∩ X := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mp hx |>.1, h_in_X hx⟩
  have h_sub₂ : T₁ ∩ T₂ ⊆ T₂ ∩ X := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mp hx |>.2, h_in_X hx⟩
  -- Both T₁ ∩ X and T₂ ∩ X have exactly 2 elements, and contain T₁ ∩ T₂ which has ≥ 2
  have h_eq₁ := Finset.eq_of_subset_of_card_le h_sub₁ (by linarith)
  have h_eq₂ := Finset.eq_of_subset_of_card_le h_sub₂ (by linarith)
  exact h_eq₁.symm.trans h_eq₂

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: All externals share a common vertex
-- ══════════════════════════════════════════════════════════════════════════════

theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T := by
  by_cases h_all_same_outside : ∀ T1 ∈ externals, ∀ T2 ∈ externals, T1 \ X = T2 \ X
  · -- All externals have same outside vertex v
    obtain ⟨T₀, hT₀⟩ := h_nonempty
    have hT₀_ext : isExternalOf G M X T₀ := h_ext T₀ hT₀
    have hT₀_out : (T₀ \ X).card = 1 := external_has_one_outside G M X hX hX_3 T₀ hT₀_ext
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hT₀_out
    use v
    intro T hT
    have h_eq := h_all_same_outside T hT T₀ hT₀
    have hv_T₀ : v ∈ T₀ \ X := by rw [hv]; exact Finset.mem_singleton_self v
    have hv_T : v ∈ T \ X := by rw [h_eq]; exact hv_T₀
    exact Finset.mem_sdiff.mp hv_T |>.1
  · -- Some externals have different outside vertices, so all share same X-edge
    push_neg at h_all_same_outside
    obtain ⟨T1, hT1, T2, hT2, h_diff⟩ := h_all_same_outside
    have hT1_ext : isExternalOf G M X T1 := h_ext T1 hT1
    have hT1_inter_card : (T1 ∩ X).card = 2 := by
      have h1 := external_has_one_outside G M X hX hX_3 T1 hT1_ext
      have h2 := Finset.card_sdiff_add_card_inter T1 X
      have h3 := triangle_card_three G T1 hT1_ext.1
      omega
    -- All externals share the same X-edge as T1
    have hS : ∀ T ∈ externals, T ∩ X = T1 ∩ X := by
      intro T hT
      by_cases h_cases : T \ X = T1 \ X
      · -- T and T1 have same outside vertex, but T2 differs
        have h_diff' : T \ X ≠ T2 \ X := by rwa [h_cases]
        have h1 := externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T2
                    (h_ext T hT) (h_ext T2 hT2) h_diff'
        have h2 := externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T1 T2
                    (h_ext T1 hT1) (h_ext T2 hT2) h_diff
        exact h1.trans h2.symm
      · -- T has different outside vertex from T1
        exact externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T1
                (h_ext T hT) (h_ext T1 hT1) h_cases
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by linarith : 0 < (T1 ∩ X).card)
    use u
    intro T hT
    have h_eq : T ∩ X = T1 ∩ X := hS T hT
    have hu_in_TX : u ∈ T ∩ X := h_eq.symm ▸ hu
    exact Finset.mem_of_mem_inter_left hu_in_TX

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Two edges cover X and all its externals
-- ══════════════════════════════════════════════════════════════════════════════

theorem two_edges_cover_X_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  have hX_clique : X ∈ G.cliqueFinset 3 := hM.1.1 hX
  rw [Finset.card_eq_three] at hX_3
  obtain ⟨a, b, c, hab, hac, hbc, hX_eq⟩ := hX_3
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hX_clique
  use s(a, b), s(a, c)
  refine ⟨?_, ?_, ?_⟩
  · -- e₁ ∈ G.edgeFinset
    apply SimpleGraph.mem_edgeFinset.mpr
    apply hclique.1
    · rw [hX_eq]; simp
    · rw [hX_eq]; simp
    · exact hab
  · -- e₂ ∈ G.edgeFinset
    apply SimpleGraph.mem_edgeFinset.mpr
    apply hclique.1
    · rw [hX_eq]; simp
    · rw [hX_eq]; simp
    · exact hac
  · -- Coverage
    intro T hT hT_clique
    rcases hT with rfl | hT_ext
    · -- T = X
      left
      rw [hX_eq, Finset.mem_sym2_iff]
      intro z hz
      simp only [Sym2.mem_iff] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hz with rfl | rfl <;> tauto
    · -- T is external: contains edge {a,b} or {a,c}
      have h_share : sharesEdgeWith T X := hT_ext.2.2.1
      have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
      -- Get two vertices from T ∩ X
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h_TX
      have hu_T := Finset.mem_inter.mp hu |>.1
      have hv_T := Finset.mem_inter.mp hv |>.1
      have hu_X := Finset.mem_inter.mp hu |>.2
      have hv_X := Finset.mem_inter.mp hv |>.2
      -- u, v ∈ X = {a, b, c} and u ≠ v
      rw [hX_eq] at hu_X hv_X
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu_X hv_X
      -- The edge {u, v} is one of {a,b}, {a,c}, {b,c}
      -- {a,b} or {a,c} must cover T since any 2 of 3 vertices include a
      rcases hu_X with rfl | rfl | rfl <;> rcases hv_X with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl huv
        | (left; rw [Finset.mem_sym2_iff]; intro z hz; simp only [Sym2.mem_iff] at hz;
           rcases hz with rfl | rfl <;> assumption)
        | (right; rw [Finset.mem_sym2_iff]; intro z hz; simp only [Sym2.mem_iff] at hz;
           rcases hz with rfl | rfl <;> assumption)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 (SINGLE SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

Every triangle T in G falls into one of three categories:
1. T ∈ M (one of the 4 packing elements)
2. T is external to exactly one X ∈ M (shares edge with X, not with others)
3. T is a bridge triangle (shares edges with multiple M-elements)

Coverage strategy:
For each X ∈ M, use two_edges_cover_X_and_externals to get edges e₁_X, e₂_X.
These 8 edges (4 elements × 2 edges) cover:

- Category 1: Each X ∈ M is covered by its own e₁_X, e₂_X
- Category 2: Each X-external is covered by e₁_X or e₂_X (proven above)
- Category 3: Bridge triangles T between X and Y:
  * By maximality, T shares edge with some M-element (proven)
  * The 8 edges include edges for all 4 M-elements
  * T is covered by whichever M-element it shares an edge with

The key is that every triangle in G either:
- Is in M → covered by that element's 2 edges
- Shares edge with exactly one M-element → covered as external
- Shares edges with 2+ M-elements → covered by any one of them
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
