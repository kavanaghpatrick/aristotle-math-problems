/-
  slot436_not_all_three_fixed.lean

  CRITICAL LEMMA: For ν = 4 packing, at most 2 of 3 external types are nonempty.

  FIXES from slot435:
  1. Added `open scoped BigOperators Classical`
  2. Changed isTrianglePacking to use Set.Pairwise (more prover-friendly)
  3. Lowered maxHeartbeats to 200000
  4. Simplified proof structure

  PROOF SKETCH:
  1. Assume all 3 external types are nonempty for element E = {v, a, b}
  2. Pick T_va from type v-a, T_vb from type v-b
  3. T_va ≠ T_vb (if equal, T contains {v,a,b} = E, contradiction)
  4. M' = M.erase E ∪ {T_va, T_vb} has size 5, contradicting ν = 4

  TIER: 2-3
-/

import Mathlib

set_option maxHeartbeats 200000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (using Set.Pairwise for prover efficiency)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Triangles containing edge {u, v} that are edge-disjoint from M\{E} -/
def ExternalsOfType (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) (u v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ E ∧ u ∈ T ∧ v ∈ T ∧ ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_mem_clique {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    T ∈ G.cliqueFinset 3 :=
  (mem_filter.mp hT).1

lemma external_ne_E {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    T ≠ E :=
  (mem_filter.mp hT).2.1

lemma external_contains_u {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    u ∈ T :=
  (mem_filter.mp hT).2.2.1

lemma external_contains_v {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    v ∈ T :=
  (mem_filter.mp hT).2.2.2.1

lemma external_disjoint {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v)
    {F : Finset V} (hF : F ∈ M) (hFE : F ≠ E) :
    (T ∩ F).card ≤ 1 :=
  (mem_filter.mp hT).2.2.2.2 F hF hFE

lemma clique3_card {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Finset V} (hT : T ∈ G.cliqueFinset 3) :
    T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT
  exact hT.2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: External not in M
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_not_in_M {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} (hM : isTrianglePacking G M)
    {E : Finset V} (hE : E ∈ M) {u v : V}
    (hu : u ∈ E) (hv : v ∈ E) (huv : u ≠ v)
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    T ∉ M := by
  intro hTM
  have hT_ne_E := external_ne_E hT
  have hu_T := external_contains_u hT
  have hv_T := external_contains_v hT
  have h_inter : {u, v} ⊆ T ∩ E := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> exact ⟨‹_›, ‹_›⟩
  have h_card : (T ∩ E).card ≥ 2 := calc
    (T ∩ E).card ≥ ({u, v} : Finset V).card := card_le_card h_inter
    _ = 2 := card_pair huv
  have h_packing := hM.2 hTM hE hT_ne_E
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem not_all_three_external_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hν_max : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ 4)
    (E : Finset V) (hE : E ∈ M)
    (v a b : V) (hE_eq : E = {v, a, b})
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    ¬((ExternalsOfType G M E v a).Nonempty ∧
      (ExternalsOfType G M E v b).Nonempty ∧
      (ExternalsOfType G M E a b).Nonempty) := by
  intro ⟨⟨T_va, hT_va⟩, ⟨T_vb, hT_vb⟩, _⟩

  -- Basic facts
  have hv_in_E : v ∈ E := by simp [hE_eq, hva, hvb]
  have ha_in_E : a ∈ E := by simp [hE_eq]
  have hb_in_E : b ∈ E := by simp [hE_eq]

  have hv_va := external_contains_u hT_va
  have ha_va := external_contains_v hT_va
  have hv_vb := external_contains_u hT_vb
  have hb_vb := external_contains_v hT_vb

  have hT_va_not_M : T_va ∉ M := external_not_in_M hM hE hv_in_E ha_in_E hva hT_va
  have hT_vb_not_M : T_vb ∉ M := external_not_in_M hM hE hv_in_E hb_in_E hvb hT_vb

  -- T_va ≠ T_vb: if equal, T contains {v,a,b} = E
  have hT_va_ne_vb : T_va ≠ T_vb := by
    intro h_eq
    have ha_in_Tvb : a ∈ T_vb := h_eq ▸ ha_va
    have hvab_sub : ({v, a, b} : Finset V) ⊆ T_vb := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hT_vb_card := clique3_card (external_mem_clique hT_vb)
    have h_vab_card : ({v, a, b} : Finset V).card = 3 := by
      rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
      · exact fun h => hab (mem_singleton.mp h)
      · simp only [mem_insert, mem_singleton]; push_neg; exact ⟨hva, hvb⟩
    have h_eq' : {v, a, b} = T_vb := eq_of_subset_of_card_le hvab_sub (by omega)
    exact external_ne_E hT_vb (hE_eq ▸ h_eq'.symm)

  -- Key claim: T_va and T_vb share at most 1 vertex
  have h_va_vb_disjoint : (T_va ∩ T_vb).card ≤ 1 := by
    sorry

  -- Construct M' = M.erase E ∪ {T_va, T_vb}
  set M' := M.erase E ∪ {T_va, T_vb} with hM'_def

  -- M' is a valid packing
  have hM'_packing : isTrianglePacking G M' := by
    refine ⟨?_, ?_⟩
    · intro X hX
      simp only [hM'_def, mem_union, mem_erase, mem_insert, mem_singleton] at hX
      rcases hX with ⟨_, hX⟩ | rfl | rfl
      · exact hM.1 hX
      · exact external_mem_clique hT_va
      · exact external_mem_clique hT_vb
    · intro X hX Y hY hXY
      simp only [hM'_def, Finset.mem_coe, mem_union, mem_erase, mem_insert, mem_singleton] at hX hY
      rcases hX with ⟨hXE, hXM⟩ | rfl | rfl <;> rcases hY with ⟨hYE, hYM⟩ | rfl | rfl
      · exact hM.2 hXM hYM hXY
      · rw [inter_comm]; exact external_disjoint hT_va hXM hXE
      · rw [inter_comm]; exact external_disjoint hT_vb hXM hXE
      · exact external_disjoint hT_va hYM hYE
      · exact absurd rfl hXY
      · exact h_va_vb_disjoint
      · exact external_disjoint hT_vb hYM hYE
      · rw [inter_comm]; exact h_va_vb_disjoint
      · exact absurd rfl hXY

  -- |M'| = 5
  have hM'_card : M'.card = 5 := by
    have h1 : (M.erase E).card = 3 := by simp [card_erase_of_mem hE, hM_card]
    have h2 : ({T_va, T_vb} : Finset (Finset V)).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]
      simp only [mem_singleton]; exact hT_va_ne_vb
    have h3 : Disjoint (M.erase E) {T_va, T_vb} := by
      simp only [disjoint_left, mem_erase, mem_insert, mem_singleton]
      intro X ⟨_, hXM⟩ hX
      rcases hX with rfl | rfl <;> [exact hT_va_not_M hXM; exact hT_vb_not_M hXM]
    simp only [hM'_def, card_union_of_disjoint h3, h1, h2]

  -- Contradiction
  have := hν_max M' hM'_packing
  omega

end
