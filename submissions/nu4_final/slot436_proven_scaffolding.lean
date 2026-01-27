/-
  slot436_proven_scaffolding.lean

  PROVEN BY ARISTOTLE (slot436): 3 lemmas with 0 sorry
  UUID: c3e811d4-a2a4-4214-bcd4-b833f194ada1

  These can be imported as scaffolding for future proofs.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN (1): Bridge contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    ext x; simp only [mem_inter, mem_singleton]; constructor
    · intro ⟨⟨hxT, hxE⟩, _, hxF⟩
      have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE, hxF⟩
      rw [hEF] at hx_both
      exact ⟨hxT, mem_singleton.mp hx_both⟩
    · intro ⟨hxT, hxv⟩
      have hv_mem : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      subst hxv
      exact ⟨⟨hxT, (mem_inter.mp hv_mem).1⟩, hxT, (mem_inter.mp hv_mem).2⟩
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx; simp only [mem_union, mem_inter] at hx
    cases hx with | inl h => exact h.1 | inr h => exact h.1
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
      calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
        _ = 3 := hT_card
    omega
  rw [card_pos] at h_pos
  obtain ⟨x, hx⟩ := h_pos
  simp only [mem_inter, mem_singleton] at hx
  exact hx.2 ▸ hx.1

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN (2): Sym2 membership from vertex membership
-- ══════════════════════════════════════════════════════════════════════════════

lemma sym2_mem_of_both_mem (a b : V) (T : Finset V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN (3): Middle element - one of 3 edges covers any interacting triangle
-- ══════════════════════════════════════════════════════════════════════════════

theorem middle_spine_spoke_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₁ b v₂ : V) (A C : Finset V)
    (h_v1_ne_b : v₁ ≠ b) (h_v1_ne_v2 : v₁ ≠ v₂) (h_b_ne_v2 : b ≠ v₂)
    (hAB : A ∩ {v₁, b, v₂} = {v₁})
    (hBC : ({v₁, b, v₂} : Finset V) ∩ C = {v₂})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTB : 2 ≤ (T ∩ {v₁, b, v₂}).card) :
    s(v₁, v₂) ∈ T.sym2 ∨ s(v₁, b) ∈ T.sym2 ∨ s(b, v₂) ∈ T.sym2 := by
  by_cases hv1 : v₁ ∈ T
  · by_cases hv2 : v₂ ∈ T
    · left; exact sym2_mem_of_both_mem v₁ v₂ T hv1 hv2
    · have hb : b ∈ T := by
        by_contra hb_not
        have h_sub : T ∩ {v₁, b, v₂} ⊆ {v₁} := by
          intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · rfl
          · exact absurd hx.1 hb_not
          · exact absurd hx.1 hv2
        have : (T ∩ {v₁, b, v₂}).card ≤ 1 := by
          calc (T ∩ {v₁, b, v₂}).card ≤ ({v₁} : Finset V).card := card_le_card h_sub
            _ = 1 := card_singleton _
        omega
      right; left; exact sym2_mem_of_both_mem v₁ b T hv1 hb
  · by_cases hv2 : v₂ ∈ T
    · have hb : b ∈ T := by
        by_contra hb_not
        have h_sub : T ∩ {v₁, b, v₂} ⊆ {v₂} := by
          intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · exact absurd hx.1 hv1
          · exact absurd hx.1 hb_not
          · rfl
        have : (T ∩ {v₁, b, v₂}).card ≤ 1 := by
          calc (T ∩ {v₁, b, v₂}).card ≤ ({v₂} : Finset V).card := card_le_card h_sub
            _ = 1 := card_singleton _
        omega
      right; right; exact sym2_mem_of_both_mem b v₂ T hb hv2
    · exfalso
      have h_sub : T ∩ {v₁, b, v₂} ⊆ {b} := by
        intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 hv1
        · rfl
        · exact absurd hx.1 hv2
      have : (T ∩ {v₁, b, v₂}).card ≤ 1 := by
        calc (T ∩ {v₁, b, v₂}).card ≤ ({b} : Finset V).card := card_le_card h_sub
          _ = 1 := card_singleton _
      omega

end
