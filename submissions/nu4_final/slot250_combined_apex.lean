/-
  slot250_combined_apex.lean

  COMBINED FILE: Includes all proven code from slot182 + slot224f
  PLUS: same_edge_share_external_vertex lemma (1 SORRY)
  PLUS: all_externals_share_apex theorem (uses same_edge lemma)

  This file is SELF-CONTAINED - Aristotle has NO external context.
-/

import Mathlib

set_option maxHeartbeats 400000

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
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING LEMMAS (from slot182/slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: 5-PACKING CONSTRUCTION (from slot182)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Two externals share an edge (slot182)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Unique outside vertex helper (slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Different edges share external vertex (slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

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
  have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_card : (T₁ ∩ T₂).card ≥ 2 := shares_edge_implies_two_vertices T₁ T₂ h_share
  have hT₁_A : (T₁ ∩ A).card = 2 := by
    have h_ge : (T₁ ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T₁ A hT₁.2.2.1
    have h_le : (T₁ ∩ A).card ≤ 2 := by
      by_contra h_gt; push_neg at h_gt
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
      by_contra h_gt; push_neg at h_gt
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
      by_contra h_ge_2; push_neg at h_ge_2
      have h_eq : T₁ ∩ A = T₂ ∩ A := by
        have h1 : (T₁ ∩ A) ∩ (T₂ ∩ A) ⊆ T₁ ∩ A := Finset.inter_subset_left
        have h2 : (T₁ ∩ A) ∩ (T₂ ∩ A) ⊆ T₂ ∩ A := Finset.inter_subset_right
        have hcard1 : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card = (T₁ ∩ A).card := by
          have := Finset.card_le_card h1; linarith
        have hcard2 : ((T₁ ∩ A) ∩ (T₂ ∩ A)).card = (T₂ ∩ A).card := by
          have := Finset.card_le_card h2; linarith
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
      · apply Finset.mem_union.mpr; left
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hv₁, hv_A⟩, Finset.mem_inter.mpr ⟨hv₂, hv_A⟩⟩
      · have hv_x₁ : v = x₁ := hx₁_unique v ⟨hv₁, hv_A⟩
        have hv_x₂ : v = x₂ := hx₂_unique v ⟨hv₂, hv_A⟩
        exact absurd (hv_x₁.symm.trans hv_x₂) h_ne_x
    have h_x_inter : ({x₁} ∩ {x₂} : Finset V) = ∅ := by
      ext v; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.not_mem_empty, iff_false]
      intro ⟨hv₁, hv₂⟩; exact h_ne_x (hv₁.symm.trans hv₂)
    rw [h_x_inter, Finset.union_empty] at h_subset
    have h_bound : (T₁ ∩ T₂).card ≤ ((T₁ ∩ A) ∩ (T₂ ∩ A)).card := Finset.card_le_card h_subset
    linarith
  use x₁
  exact ⟨hx₁_not_A, hx₁_T₁, h_x_eq ▸ hx₂_T₂⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW LEMMA: Same-edge externals share external vertex (1 SORRY FOR ARISTOTLE)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Externals using the SAME edge of A also share their external vertex.
    The shared edge {u,v} from T₁ ∩ T₂ must include an external vertex,
    since both triangles use the same A-edge (so the A-part doesn't distinguish them). -/
lemma same_edge_share_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂)
    (h_same_edge : T₁ ∩ A = T₂ ∩ A) :
    ∃ x : V, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- T₁ and T₂ share an edge {u, v} (by two_externals_share_edge)
  have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  obtain ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩ := h_share
  -- T₁ ∩ A has exactly 2 vertices
  have hT₁_A_card : (T₁ ∩ A).card = 2 := by
    have h_ge : (T₁ ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T₁ A hT₁.2.2.1
    have h_le : (T₁ ∩ A).card ≤ 2 := by
      by_contra h; push_neg at h
      have h_sub : T₁ ⊆ A := by
        have h_inter_sub : T₁ ∩ A ⊆ T₁ := Finset.inter_subset_left
        have h_card_eq : (T₁ ∩ A).card = T₁.card := by
          have h1 : (T₁ ∩ A).card ≤ T₁.card := Finset.card_le_card h_inter_sub; linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx; exact Finset.mem_inter.mp hx |>.2
      have h_sub' : A ⊆ T₁ := by
        have h_inter_sub : T₁ ∩ A ⊆ A := Finset.inter_subset_right
        have h_card_eq : (T₁ ∩ A).card = A.card := by
          have h1 : (T₁ ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub; linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx; exact Finset.mem_inter.mp hx |>.1
      exact hT₁.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hA)
    linarith
  -- External vertex of T₁
  have h_T₁_diff : (T₁ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₁ A; rw [hT₁_A_card, hT₁_3] at this; omega
  obtain ⟨x₁, hx₁_eq⟩ := Finset.card_eq_one.mp h_T₁_diff
  have hx₁_T₁ : x₁ ∈ T₁ := by
    have : x₁ ∈ T₁ \ A := by rw [hx₁_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.1
  have hx₁_not_A : x₁ ∉ A := by
    have : x₁ ∈ T₁ \ A := by rw [hx₁_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.2
  -- External vertex of T₂
  have hT₂_A_card : (T₂ ∩ A).card = 2 := by rw [← h_same_edge]; exact hT₁_A_card
  have h_T₂_diff : (T₂ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₂ A; rw [hT₂_A_card, hT₂_3] at this; omega
  obtain ⟨x₂, hx₂_eq⟩ := Finset.card_eq_one.mp h_T₂_diff
  have hx₂_T₂ : x₂ ∈ T₂ := by
    have : x₂ ∈ T₂ \ A := by rw [hx₂_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.1
  have hx₂_not_A : x₂ ∉ A := by
    have : x₂ ∈ T₂ \ A := by rw [hx₂_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.2
  -- The shared edge {u, v} must involve x₁ or x₂
  -- Since T₁ = (T₁ ∩ A) ∪ {x₁} and T₂ = (T₂ ∩ A) ∪ {x₂}
  -- And T₁ ∩ A = T₂ ∩ A, if u,v ∈ T₁ ∩ A, then T₁ and T₂ share exactly those 2 vertices
  -- But T₁ ≠ T₂, so one of u,v must be an external vertex
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: All externals share a common apex
-- ══════════════════════════════════════════════════════════════════════════════

/-- All externals of a single M-element share a common external vertex (apex) -/
theorem all_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (h_nonempty : (externalsOf G M A).Nonempty) :
    ∃ x : V, x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T := by
  obtain ⟨T₀, hT₀⟩ := h_nonempty
  have hT₀_ext : isExternalOf G M A T₀ := Finset.mem_filter.mp hT₀ |>.2
  have hT₀_3 : T₀.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₀_ext.1 |>.2
  have hT₀_A_card : (T₀ ∩ A).card = 2 := by
    have h_ge : (T₀ ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T₀ A hT₀_ext.2.2.1
    have h_le : (T₀ ∩ A).card ≤ 2 := by
      by_contra h; push_neg at h
      have h_sub : T₀ ⊆ A := by
        have h_inter_sub : T₀ ∩ A ⊆ T₀ := Finset.inter_subset_left
        have h_card_eq : (T₀ ∩ A).card = T₀.card := by
          have h1 : (T₀ ∩ A).card ≤ T₀.card := Finset.card_le_card h_inter_sub; linarith
        intro w hw
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hw; exact Finset.mem_inter.mp hw |>.2
      have h_sub' : A ⊆ T₀ := by
        have h_inter_sub : T₀ ∩ A ⊆ A := Finset.inter_subset_right
        have h_card_eq : (T₀ ∩ A).card = A.card := by
          have h1 : (T₀ ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub; linarith
        intro w hw
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hw; exact Finset.mem_inter.mp hw |>.1
      exact hT₀_ext.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hA)
    linarith
  have h_T₀_diff : (T₀ \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₀ A; rw [hT₀_A_card, hT₀_3] at this; omega
  obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp h_T₀_diff
  have hx_T₀ : x ∈ T₀ := by
    have : x ∈ T₀ \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.1
  have hx_not_A : x ∉ A := by
    have : x ∈ T₀ \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_sdiff.mp this |>.2
  use x
  constructor
  · exact hx_not_A
  · intro T hT
    have hT_ext : isExternalOf G M A T := Finset.mem_filter.mp hT |>.2
    have hT_3 : T.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT_ext.1 |>.2
    by_cases h_eq : T = T₀
    · rw [h_eq]; exact hx_T₀
    · by_cases h_same : T ∩ A = T₀ ∩ A
      · obtain ⟨y, hy_not_A, hy_T, hy_T₀⟩ := same_edge_share_external_vertex G M hM hM_card hν A hA hA_3 T T₀ hT_ext hT₀_ext hT_3 hT₀_3 h_eq h_same
        have hy_unique_T₀ : y = x := by
          have : y ∈ T₀ \ A := Finset.mem_sdiff.mpr ⟨hy_T₀, hy_not_A⟩
          rw [hx_eq] at this; exact Finset.mem_singleton.mp this
        rw [← hy_unique_T₀]; exact hy_T
      · obtain ⟨y, hy_not_A, hy_T, hy_T₀⟩ := different_edges_share_external_vertex G M hM hM_card hν A hA hA_3 T T₀ hT_ext hT₀_ext hT_3 hT₀_3 h_eq h_same
        have hy_unique_T₀ : y = x := by
          have : y ∈ T₀ \ A := Finset.mem_sdiff.mpr ⟨hy_T₀, hy_not_A⟩
          rw [hx_eq] at this; exact Finset.mem_singleton.mp this
        rw [← hy_unique_T₀]; exact hy_T

end
