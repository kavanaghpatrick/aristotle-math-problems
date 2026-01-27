/-
  slot433_not_all_three_external_types.lean

  CRITICAL LEMMA: For ν = 4 packing, at most 2 of 3 external types are nonempty.

  PROOF SKETCH:
  1. Assume all 3 external types are nonempty for element E = {v, a, b}
  2. Pick one triangle from each type: T_va, T_vb, T_ab
  3. T_va ≠ T_vb because T_va contains a, T_vb contains b, and a ≠ b
  4. M' = M.erase E ∪ {T_va, T_vb} is a valid packing of size 5
  5. Contradiction with ν = 4

  TIER: 2-3 (pigeonhole + disjointness)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Triangles sharing a specific edge {u, v} with element E -/
def ExternalsOfType (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) (u v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ E ∧
    u ∈ T ∧ v ∈ T ∧
    ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- External membership gives clique membership -/
lemma external_is_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) (u v : V)
    (T : Finset V) (hT : T ∈ ExternalsOfType G M E u v) :
    T ∈ G.cliqueFinset 3 := by
  simp only [ExternalsOfType, mem_filter] at hT
  exact hT.1

/-- External membership gives vertex containment -/
lemma external_contains_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) (u v : V)
    (T : Finset V) (hT : T ∈ ExternalsOfType G M E u v) :
    u ∈ T ∧ v ∈ T := by
  simp only [ExternalsOfType, mem_filter] at hT
  exact ⟨hT.2.2.1, hT.2.2.2.1⟩

/-- External membership gives disjointness from other packing elements -/
lemma external_disjoint_from_others (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) (u v : V)
    (T : Finset V) (hT : T ∈ ExternalsOfType G M E u v)
    (F : Finset V) (hF : F ∈ M) (hFE : F ≠ E) :
    (T ∩ F).card ≤ 1 := by
  simp only [ExternalsOfType, mem_filter] at hT
  exact hT.2.2.2.2 F hF hFE

/-- External is not E -/
lemma external_ne_E (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) (u v : V)
    (T : Finset V) (hT : T ∈ ExternalsOfType G M E u v) :
    T ≠ E := by
  simp only [ExternalsOfType, mem_filter] at hT
  exact hT.2.1

/-- External is not in M (because it would share 2+ vertices with E) -/
lemma external_not_in_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (E : Finset V) (hE : E ∈ M) (u v : V)
    (hu : u ∈ E) (hv : v ∈ E) (huv : u ≠ v)
    (T : Finset V) (hT : T ∈ ExternalsOfType G M E u v) :
    T ∉ M := by
  intro hT_in_M
  have hT_ne_E := external_ne_E G M E u v T hT
  have ⟨hu_T, hv_T⟩ := external_contains_vertices G M E u v T hT
  have h_pairwise := hM.2 hT_in_M hE hT_ne_E
  have h_card : (T ∩ E).card ≥ 2 := by
    have hu_inter : u ∈ T ∩ E := mem_inter.mpr ⟨hu_T, hu⟩
    have hv_inter : v ∈ T ∩ E := mem_inter.mpr ⟨hv_T, hv⟩
    have h_two : ({u, v} : Finset V) ⊆ T ∩ E := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h_pair_card : ({u, v} : Finset V).card = 2 := by
      rw [card_pair huv]
    calc (T ∩ E).card ≥ ({u, v} : Finset V).card := card_le_card h_two
      _ = 2 := h_pair_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Assume all 3 types are nonempty: ∃ T_va ∈ Type_va, T_vb ∈ Type_vb, T_ab ∈ Type_ab
2. T_va, T_vb are edge-disjoint (share only v)
3. T_va ≠ T_vb (T_va contains a, T_vb contains b, a ≠ b)
4. M' = M.erase E ∪ {T_va, T_vb} is a valid packing
5. |M'| = |M| - 1 + 2 = 5
6. Contradiction with ν = 4
-/

theorem not_all_three_external_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (E : Finset V) (hE : E ∈ M)
    (v a b : V) (hE_eq : E = {v, a, b})
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    ¬((ExternalsOfType G M E v a).Nonempty ∧
      (ExternalsOfType G M E v b).Nonempty ∧
      (ExternalsOfType G M E a b).Nonempty) := by
  intro ⟨⟨T_va, hT_va⟩, ⟨T_vb, hT_vb⟩, ⟨T_ab, hT_ab⟩⟩

  -- Get clique properties
  have hT_va_clq : T_va ∈ G.cliqueFinset 3 := external_is_clique G M E v a T_va hT_va
  have hT_vb_clq : T_vb ∈ G.cliqueFinset 3 := external_is_clique G M E v b T_vb hT_vb

  -- Get vertex containment
  have ⟨hv_va, ha_va⟩ := external_contains_vertices G M E v a T_va hT_va
  have ⟨hv_vb, hb_vb⟩ := external_contains_vertices G M E v b T_vb hT_vb

  -- T_va ∉ M and T_vb ∉ M
  have hv_in_E : v ∈ E := by rw [hE_eq]; simp
  have ha_in_E : a ∈ E := by rw [hE_eq]; simp
  have hb_in_E : b ∈ E := by rw [hE_eq]; simp

  have hT_va_not_M : T_va ∉ M := external_not_in_M G M hM E hE v a hv_in_E ha_in_E hva T_va hT_va
  have hT_vb_not_M : T_vb ∉ M := external_not_in_M G M hM E hE v b hv_in_E hb_in_E hvb T_vb hT_vb

  -- T_va and T_vb are edge-disjoint (share at most 1 vertex)
  -- This is the key claim that Aristotle should prove
  have h_va_vb_disjoint : (T_va ∩ T_vb).card ≤ 1 := by
    sorry

  -- T_va ≠ T_vb (because T_va contains a, T_vb contains b, and if equal then
  -- the triangle would contain {v, a, b} = E, contradicting T_va ≠ E)
  have hT_va_ne_vb : T_va ≠ T_vb := by
    intro h_eq
    have hT_va_ne_E := external_ne_E G M E v a T_va hT_va
    rw [h_eq] at ha_va
    -- Now a ∈ T_vb, v ∈ T_vb, b ∈ T_vb
    -- So {v, a, b} ⊆ T_vb
    have h_sub : ({v, a, b} : Finset V) ⊆ T_vb := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv_vb
      · exact ha_va
      · exact hb_vb
    -- |{v, a, b}| = 3 = |T_vb|, so T_vb = {v, a, b} = E
    have hT_vb_card : T_vb.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT_vb_clq
      exact hT_vb_clq.2
    have h_E_card : ({v, a, b} : Finset V).card = 3 := by
      rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
      · simp [hab]
      · simp [hva, hvb]
    have h_eq' : {v, a, b} = T_vb := by
      apply Finset.eq_of_subset_of_card_le h_sub
      rw [h_E_card, hT_vb_card]
    rw [← hE_eq, ← h_eq] at h_eq'
    exact hT_va_ne_E h_eq'.symm

  -- M' = M.erase E ∪ {T_va, T_vb} is a valid packing of size 5
  let M' := M.erase E ∪ {T_va, T_vb}

  -- Show M' is a valid packing
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · -- Subset of cliques
      intro X hX
      simp only [mem_union, mem_erase, mem_insert, mem_singleton] at hX
      rcases hX with ⟨_, hX_M⟩ | rfl | rfl
      · exact hM.1 hX_M
      · exact hT_va_clq
      · exact hT_vb_clq
    · -- Pairwise edge-disjoint
      intro X hX Y hY hXY
      simp only [Set.mem_coe, Finset.coe_union, Set.mem_union, Finset.mem_coe,
                 mem_erase, mem_insert, mem_singleton] at hX hY
      rcases hX with ⟨hX_ne_E, hX_M⟩ | rfl | rfl
      · rcases hY with ⟨hY_ne_E, hY_M⟩ | rfl | rfl
        · exact hM.2 hX_M hY_M hXY
        · exact external_disjoint_from_others G M E v a T_va hT_va X hX_M hX_ne_E
        · exact external_disjoint_from_others G M E v b T_vb hT_vb X hX_M hX_ne_E
      · rcases hY with ⟨hY_ne_E, hY_M⟩ | rfl | rfl
        · rw [inter_comm]; exact external_disjoint_from_others G M E v a T_va hT_va Y hY_M hY_ne_E
        · exact absurd rfl hXY
        · exact h_va_vb_disjoint
      · rcases hY with ⟨hY_ne_E, hY_M⟩ | rfl | rfl
        · rw [inter_comm]; exact external_disjoint_from_others G M E v b T_vb hT_vb Y hY_M hY_ne_E
        · rw [inter_comm]; exact h_va_vb_disjoint
        · exact absurd rfl hXY

  -- Count: |M'| = 5
  have hM'_card : M'.card = 5 := by
    have h_erase_card : (M.erase E).card = 3 := by
      rw [card_erase_of_mem hE, hM_card]
    have h_pair_card : ({T_va, T_vb} : Finset (Finset V)).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]
      simp only [mem_singleton]
      exact hT_va_ne_vb
    have h_disjoint : Disjoint (M.erase E) {T_va, T_vb} := by
      rw [Finset.disjoint_left]
      intro X hX hX_pair
      simp only [mem_erase] at hX
      simp only [mem_insert, mem_singleton] at hX_pair
      rcases hX_pair with rfl | rfl
      · exact hT_va_not_M hX.2
      · exact hT_vb_not_M hX.2
    calc M'.card = (M.erase E ∪ {T_va, T_vb}).card := rfl
      _ = (M.erase E).card + ({T_va, T_vb} : Finset _).card := card_union_of_disjoint h_disjoint
      _ = 3 + 2 := by rw [h_erase_card, h_pair_card]
      _ = 5 := by norm_num

  -- M' is a packing of size 5, contradicting that M was a maximum packing of size 4
  -- This requires an additional hypothesis that ν(G) = 4
  sorry

end
