/-
  slot227_bridge_externals_minimal.lean

  THE MAKE-OR-BREAK LEMMA FOR τ ≤ 8

  Clean minimal version with exactly 1 sorry.
  All scaffolding from proven slot224f.

  Key question: Do externals of DIFFERENT M-elements at shared vertex v
  share a common external apex?

  If TRUE → τ ≤ 8 achievable
  If FALSE (counterexample) → τ ≤ 12 is best via this approach
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot224f PROVEN)
-- ═══════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot224f)
-- ═══════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  have hu_inter : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu_m⟩
  have hv_inter : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv_m⟩
  exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

lemma not_share_implies_one_vertex (t m : Finset V)
    (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact h_not_share ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  exact not_share_implies_one_vertex t B (ht_ext.2.2.2 B hB hAB.symm)

-- ═══════════════════════════════════════════════════════════════════════
-- 5-PACKING (from slot182 PROVEN)
-- ═══════════════════════════════════════════════════════════════════════

theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_no_shared_edge : ¬sharesEdgeWith T₁ T₂) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M' := by
  let M' := {T₁, T₂} ∪ M.erase A
  use M'
  have hT₁_not_M : T₁ ∉ M := hT₁.2.1
  have hT₂_not_M : T₂ ∉ M := hT₂.2.1
  constructor
  · have h1 : (M.erase A).card = 3 := by rw [Finset.card_erase_of_mem hA]; omega
    have h2 : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp only [Finset.mem_singleton]; exact hT₁_ne_T₂
    have h3 : Disjoint {T₁, T₂} (M.erase A) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · intro h; exact hT₁_not_M (Finset.mem_erase.mp (h ▸ hy)).2
      · intro h; exact hT₂_not_M (Finset.mem_erase.mp (h ▸ hy)).2
    rw [Finset.card_union_of_disjoint h3, h2, h1]
  · constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with hp | hm
      · rcases Finset.mem_insert.mp hp with rfl | hs
        · exact hT₁.1
        · rw [Finset.mem_singleton] at hs; rw [hs]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp hm).2
    · intro t₁ ht₁ t₂ ht₂ hne
      rcases Finset.mem_union.mp ht₁ with hp₁ | hm₁ <;>
      rcases Finset.mem_union.mp ht₂ with hp₂ | hm₂
      · rcases Finset.mem_insert.mp hp₁ with heq₁ | hs₁ <;>
        rcases Finset.mem_insert.mp hp₂ with heq₂ | hs₂
        · exact absurd (heq₁.trans heq₂.symm) hne
        · rw [Finset.mem_singleton] at hs₂; rw [heq₁, hs₂]
          exact not_share_implies_one_vertex T₁ T₂ h_no_shared_edge
        · rw [Finset.mem_singleton] at hs₁; rw [hs₁, heq₂, Finset.inter_comm]
          exact not_share_implies_one_vertex T₁ T₂ h_no_shared_edge
        · rw [Finset.mem_singleton] at hs₁ hs₂
          exact absurd (hs₁.trans hs₂.symm) hne
      · have hB := (Finset.mem_erase.mp hm₂).2
        have hB_ne := (Finset.mem_erase.mp hm₂).1
        rcases Finset.mem_insert.mp hp₁ with heq₁ | hs₁
        · rw [heq₁]; exact external_intersects_other_le_1 G M A t₂ hB hB_ne.symm T₁ hT₁
        · rw [Finset.mem_singleton] at hs₁; rw [hs₁]
          exact external_intersects_other_le_1 G M A t₂ hB hB_ne.symm T₂ hT₂
      · have hB := (Finset.mem_erase.mp hm₁).2
        have hB_ne := (Finset.mem_erase.mp hm₁).1
        rcases Finset.mem_insert.mp hp₂ with heq₂ | hs₂
        · rw [heq₂, Finset.inter_comm]
          exact external_intersects_other_le_1 G M A t₁ hB hB_ne.symm T₁ hT₁
        · rw [Finset.mem_singleton] at hs₂; rw [hs₂, Finset.inter_comm]
          exact external_intersects_other_le_1 G M A t₁ hB hB_ne.symm T₂ hT₂
      · exact hM.1.2 (Finset.mem_erase.mp hm₁).2 (Finset.mem_erase.mp hm₂).2 hne

-- ═══════════════════════════════════════════════════════════════════════
-- TWO EXTERNALS SHARE EDGE (from slot182 PROVEN)
-- ═══════════════════════════════════════════════════════════════════════

theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_no_edge
  have := hν M' hM'_packing
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- THE MAKE-OR-BREAK LEMMA (1 SORRY)
-- ═══════════════════════════════════════════════════════════════════════

/--
  Bridge Externals Share Apex

  If T₁ is external of A at shared vertex v, and T₂ is external of B at v,
  do they share a common external vertex x (where x ∉ A ∧ x ∉ B)?

  Key insight from debate:
  - The naive 5-packing argument does NOT work here
  - T₁ external of A, T₂ external of B (different M-elements)
  - Replacing A,B with T₁,T₂ gives {T₁, T₂, C, D} = 4 elements (not 5!)

  Proof strategies for Aristotle:
  1. Show T₁ and T₂ must share an edge (extending slot182)
  2. Use cycle_4 structure constraints
  3. Find a 5th triangle to contradict ν = 4
  4. OR find counterexample graph where x₁ ≠ x₂ with ν = 4
-/
theorem bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  sorry

end
