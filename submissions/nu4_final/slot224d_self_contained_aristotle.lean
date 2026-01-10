/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9f49c579-ba4a-4842-ad48-95091ebfd294
-/

/-
  slot224d_self_contained.lean

  GOAL: Prove different_edges_share_external_vertex using slot182's 5-packing proof.

  This version is SELF-CONTAINED - no axioms. It includes the full slot182 proof
  and builds the new lemma on top of it.

  KEY THEOREM: different_edges_share_external_vertex
    If T₁, T₂ are externals of A using different edges of A, they share x ∉ A.

  1 SORRY for Aristotle (the new lemma only).
-/

import Mathlib


set_option maxHeartbeats 400000

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
-- SCAFFOLDING LEMMAS (proven in slot182)
-- ══════════════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_share : sharesEdgeWith t m) :
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
  have h2 : (t ∩ m).card ≥ 2 := h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  have hu_t : u ∈ t := (Finset.mem_inter.mp hu).1
  have hu_m : u ∈ m := (Finset.mem_inter.mp hu).2
  have hv_t : v ∈ t := (Finset.mem_inter.mp hv).1
  have hv_m : v ∈ m := (Finset.mem_inter.mp hv).2
  exact h_not_share ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩

lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  have ht_3 : t.card = 3 := by
    have : t ∈ G.cliqueFinset 3 := ht_ext.1
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2
  have hB_3 : B.card = 3 := by
    have : B ∈ G.cliqueFinset 3 := hM.1.1 hB
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2
  have h_not_share : ¬sharesEdgeWith t B := ht_ext.2.2.2 B hB hAB.symm
  exact not_share_implies_one_vertex t B ht_3 hB_3 h_not_share

lemma edge_disjoint_implies_one_vertex (T₁ T₂ : Finset V)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    (T₁ ∩ T₂).card ≤ 1 := by
  have h_not_share : ¬sharesEdgeWith T₁ T₂ := by
    intro ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
    exact h_edge_disj u v huv hu₁ hv₁ hu₂ hv₂
  exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- 5-PACKING CONSTRUCTION (proven in slot182)
-- ══════════════════════════════════════════════════════════════════════════════

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
  have hM_minus_A_card : M_minus_A.card = 3 := by
    rw [Finset.card_erase_of_mem hA]
    omega
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
        · rw [Finset.mem_singleton] at ht_sing
          rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MA).2
    · intro t₁ ht₁ t₂ ht₂ h_ne
      have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
      have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
      have ht₁' := Finset.mem_union.mp ht₁
      have ht₂' := Finset.mem_union.mp ht₂
      rcases ht₁' with ht₁_pair | ht₁_MA <;> rcases ht₂' with ht₂_pair | ht₂_MA
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne
          · rw [Finset.mem_singleton] at ht₂_sing
            rw [heq₁, ht₂_sing]
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
          exact external_intersects_other_le_1 G M hM A t₂ hA hB_M hB_ne_A.symm T₁ hT₁
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          exact external_intersects_other_le_1 G M hM A t₂ hA hB_M hB_ne_A.symm T₂ hT₂
      · have hB_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have hB_ne_A : t₁ ≠ A := (Finset.mem_erase.mp ht₁_MA).1
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂]
          have h := external_intersects_other_le_1 G M hM A t₁ hA hB_M hB_ne_A.symm T₁ hT₁
          rw [Finset.inter_comm] at h; exact h
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing]
          have h := external_intersects_other_le_1 G M hM A t₁ hA hB_M hB_ne_A.symm T₂ hT₂
          rw [Finset.inter_comm] at h; exact h
      · have ht₁_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have ht₂_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        exact hM.1.2 ht₁_M ht₂_M h_ne

-- ══════════════════════════════════════════════════════════════════════════════
-- SLOT182: Two externals share an edge (PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW LEMMA: External has unique outside vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_has_unique_outside_vertex (T A : Finset V)
    (hT_3 : T.card = 3) (hA_3 : A.card = 3) (hTA : (T ∩ A).card = 2) :
    ∃! x, x ∈ T ∧ x ∉ A := by
  have h_diff : (T \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T A
    omega
  rw [Finset.card_eq_one] at h_diff
  obtain ⟨x, hx_eq⟩ := h_diff
  use x
  constructor
  · constructor
    · have : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
      exact Finset.mem_sdiff.mp this |>.1
    · have : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
      exact Finset.mem_sdiff.mp this |>.2
  · intro y ⟨hy_T, hy_not_A⟩
    have : y ∈ T \ A := Finset.mem_sdiff.mpr ⟨hy_T, hy_not_A⟩
    rw [hx_eq] at this
    exact Finset.mem_singleton.mp this

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown constant `Finset.card_inter_le_right`
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 2
where
 a := (↑(#(T₁ ∩ T₂)) : ℤ)
Unknown constant `Finset.card_inter_le_right`
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 2
where
 a := (↑(#(T₁ ∩ T₂)) : ℤ)
Application type mismatch: The argument
  hv
has type
  v ∈ T₁ ∩ A
but is expected to have type
  v ∈ T₂ ∩ A ∩ ?m.348
in the application
  Finset.mem_of_mem_inter_left hv
Unknown constant `Finset.card_inter_le_left`-/
-- ══════════════════════════════════════════════════════════════════════════════
-- NEW LEMMA: Different edges share external vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁, T₂ are externals using different edges of A, they share a common external vertex.

    Proof: T₁ = {a, b, x₁}, T₂ = {b, c, x₂} using adjacent edges {a,b}, {b,c} of A.
    They share edge (by slot182), so |T₁ ∩ T₂| ≥ 2.
    T₁ ∩ T₂ = {b} ∪ ({x₁} ∩ {x₂}) since x₁, x₂ ∉ A.
    For |T₁ ∩ T₂| ≥ 2: must have x₁ = x₂. -/
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
  -- Step 1: They share an edge (from slot182)
  have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  have h_inter : (T₁ ∩ T₂).card ≥ 2 := shares_edge_implies_two_vertices T₁ T₂ hT₁_3 hT₂_3 h_share
  -- Step 2: T₁ ∩ A and T₂ ∩ A each have 2 vertices
  have hT₁_A : (T₁ ∩ A).card = 2 := by
    have h := hT₁.2.2.1
    have h_ge : (T₁ ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T₁ A hT₁_3 hA_3 h
    have h_le : (T₁ ∩ A).card ≤ A.card := Finset.card_inter_le_right T₁ A
    omega
  have hT₂_A : (T₂ ∩ A).card = 2 := by
    have h := hT₂.2.2.1
    have h_ge : (T₂ ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T₂ A hT₂_3 hA_3 h
    have h_le : (T₂ ∩ A).card ≤ A.card := Finset.card_inter_le_right T₂ A
    omega
  -- Step 3: Get unique external vertices x₁, x₂
  obtain ⟨x₁, ⟨hx₁_T₁, hx₁_not_A⟩, hx₁_unique⟩ :=
    external_has_unique_outside_vertex T₁ A hT₁_3 hA_3 hT₁_A
  obtain ⟨x₂, ⟨hx₂_T₂, hx₂_not_A⟩, hx₂_unique⟩ :=
    external_has_unique_outside_vertex T₂ A hT₂_3 hA_3 hT₂_A
  -- Step 4: Two different 2-subsets of a 3-set share exactly 1 element
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
        apply Finset.eq_of_subset_of_card_le
        · intro v hv; exact Finset.mem_of_mem_inter_left hv
        · calc (T₂ ∩ A).card = 2 := hT₂_A
            _ ≤ ((T₁ ∩ A) ∩ (T₂ ∩ A)).card := h_ge_2
            _ ≤ (T₁ ∩ A).card := Finset.card_inter_le_left _ _
      exact h_diff_edge h_eq
    omega
  -- Step 5: x₁ = x₂ because |T₁ ∩ T₂| ≥ 2 and A-intersection is only 1
  have h_x_eq : x₁ = x₂ := by
    -- The intersection T₁ ∩ T₂ consists of:
    -- - Elements in (T₁ ∩ A) ∩ (T₂ ∩ A): exactly 1 element
    -- - Elements in T₁ \ A ∩ T₂ \ A: possibly x₁ = x₂
    -- Since |T₁ ∩ T₂| ≥ 2 and A-contribution is 1, we need x₁ = x₂
    by_contra h_ne_x
    -- Count elements in T₁ ∩ T₂
    have h_bound : (T₁ ∩ T₂).card ≤ 1 + if x₁ = x₂ then 1 else 0 := by
      -- T₁ ∩ T₂ ⊆ (T₁ ∩ A ∩ T₂ ∩ A) ∪ {x₁} ∩ {x₂}
      -- |T₁ ∩ A ∩ T₂ ∩ A| = 1
      -- |{x₁} ∩ {x₂}| = 0 if x₁ ≠ x₂
      sorry
    simp only [h_ne_x, ↓reduceIte, add_zero] at h_bound
    omega
  use x₁
  exact ⟨hx₁_not_A, hx₁_T₁, h_x_eq ▸ hx₂_T₂⟩

end