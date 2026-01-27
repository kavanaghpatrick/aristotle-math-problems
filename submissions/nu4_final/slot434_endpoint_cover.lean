/-
  slot434_endpoint_cover.lean

  ENDPOINT COVER LEMMA: 2 spokes cover endpoint + all bridges

  KEY INSIGHT:
  For endpoint A = {a₁, a₂, v₁} with adjacent B = {v₁, b, v₂}:
  - If all S_e(A) externals contain v₁, then spokes s(a₁,v₁), s(a₂,v₁) cover everything
  - This is because:
    1. A-B bridges always contain v₁ (by slot441)
    2. S_e externals contain v₁ (by hypothesis)
    3. Any T with |T ∩ A| ≥ 2 that contains v₁ is hit by some spoke

  TIER: 2 (proven helpers + single main theorem)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Bridge contains shared vertex (from slot441)
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
      rw [hxv]
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
-- HELPER: T ∩ {a,b,c} ≥ 2 with c ∈ T → a ∈ T ∨ b ∈ T
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_of_three_with_one_known (T : Finset V) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_inter : 2 ≤ (T ∩ {a, b, c}).card) (hc : c ∈ T) :
    a ∈ T ∨ b ∈ T := by
  by_contra h_neither
  push_neg at h_neither
  have h_sub : T ∩ {a, b, c} ⊆ {c} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 h_neither.1
    · exact absurd hx.1 h_neither.2
    · simp
  have h_card : (T ∩ {a, b, c}).card ≤ 1 := by
    calc (T ∩ {a, b, c}).card ≤ ({c} : Finset V).card := card_le_card h_sub
      _ = 1 := card_singleton c
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Sym2 membership from vertex membership
-- ══════════════════════════════════════════════════════════════════════════════

lemma sym2_mem_of_both_mem (a b : V) (T : Finset V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Spokes cover endpoint when externals contain spine vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Let T be any triangle with |T ∩ A| ≥ 2 where A = {a₁, a₂, v₁}
2. Case 1: T is also a bridge (|T ∩ B| ≥ 2)
   - By bridge_contains_shared, v₁ ∈ T
3. Case 2: T is not a bridge (|T ∩ B| ≤ 1)
   - By hypothesis h_ext_contains_v1, v₁ ∈ T
4. In both cases, v₁ ∈ T
5. Since |T ∩ A| ≥ 2 and v₁ ∈ T, by two_of_three, a₁ ∈ T or a₂ ∈ T
6. If a₁ ∈ T: s(a₁, v₁) ∈ T.sym2 ✓
7. If a₂ ∈ T: s(a₂, v₁) ∈ T.sym2 ✓
-/
theorem endpoint_spokes_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V) (B : Finset V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ B = {v₁})
    -- Key hypothesis: all S_e externals contain v₁
    (h_ext_contains_v1 : ∀ T ∈ G.cliqueFinset 3,
      2 ≤ (T ∩ {a₁, a₂, v₁}).card → (T ∩ B).card ≤ 1 → v₁ ∈ T)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTA : 2 ≤ (T ∩ {a₁, a₂, v₁}).card) :
    s(a₁, v₁) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
  -- First establish v₁ ∈ T
  have hv₁T : v₁ ∈ T := by
    by_cases hTB : 2 ≤ (T ∩ B).card
    · -- Bridge case
      exact bridge_contains_shared G {a₁, a₂, v₁} B v₁ hAB T hT hTA hTB
    · -- External case (not a bridge)
      push_neg at hTB
      exact h_ext_contains_v1 T hT hTA hTB
  -- Now use two_of_three to get a₁ ∈ T or a₂ ∈ T
  obtain ha1 | ha2 := two_of_three_with_one_known T a₁ a₂ v₁ h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 hTA hv₁T
  · left; exact sym2_mem_of_both_mem a₁ v₁ T ha1 hv₁T
  · right; exact sym2_mem_of_both_mem a₂ v₁ T ha2 hv₁T

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: 2 edges suffice for endpoint A
-- ══════════════════════════════════════════════════════════════════════════════

theorem endpoint_two_edges_suffice (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V) (B : Finset V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (hA : {a₁, a₂, v₁} ∈ G.cliqueFinset 3)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ B = {v₁})
    (h_ext_contains_v1 : ∀ T ∈ G.cliqueFinset 3,
      2 ≤ (T ∩ {a₁, a₂, v₁}).card → (T ∩ B).card ≤ 1 → v₁ ∈ T) :
    let Cover := ({s(a₁, v₁), s(a₂, v₁)} : Finset (Sym2 V))
    Cover.card ≤ 2 ∧
    Cover ⊆ G.edgeFinset ∧
    ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card → ∃ e ∈ Cover, e ∈ T.sym2 := by
  intro Cover
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 2
    simp only [Cover]
    by_cases h : s(a₁, v₁) = s(a₂, v₁)
    · simp [h]
    · have : ({s(a₁, v₁), s(a₂, v₁)} : Finset (Sym2 V)).card = 2 := by
        rw [card_insert_of_not_mem, card_singleton]
        simp only [mem_singleton]
        exact h
      omega
  · -- Subset of G.edgeFinset
    intro e he
    simp only [Cover, mem_insert, mem_singleton] at he
    rw [SimpleGraph.mem_edgeFinset]
    rw [SimpleGraph.mem_cliqueFinset_iff] at hA
    rcases he with rfl | rfl
    · exact hA.1 (by simp) (by simp) h_a1_ne_v1
    · exact hA.1 (by simp) (by simp) h_a2_ne_v1
  · -- Covers all triangles sharing edge with A
    intro T hT hTA
    obtain h1 | h2 := endpoint_spokes_cover G a₁ a₂ v₁ B h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 hAB h_ext_contains_v1 T hT hTA
    · use s(a₁, v₁); exact ⟨by simp [Cover], h1⟩
    · use s(a₂, v₁); exact ⟨by simp [Cover], h2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SIMILAR FOR MIDDLE ELEMENTS: spine + spoke cover
-- ══════════════════════════════════════════════════════════════════════════════

/-
For middle element B = {v₁, b, v₂} between A and C:
- A-B bridges contain v₁
- B-C bridges contain v₂
- S_e externals: use 6-packing to get ≤2 types
- If spine type (s(v₁,v₂)) is needed OR has bridges, include it
-/

theorem middle_spine_spoke_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₁ b v₂ : V) (A C : Finset V)
    (h_v1_ne_b : v₁ ≠ b) (h_v1_ne_v2 : v₁ ≠ v₂) (h_b_ne_v2 : b ≠ v₂)
    (hAB : A ∩ {v₁, b, v₂} = {v₁})
    (hBC : ({v₁, b, v₂} : Finset V) ∩ C = {v₂})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTB : 2 ≤ (T ∩ {v₁, b, v₂}).card) :
    -- At least one of these edges is in T.sym2
    s(v₁, v₂) ∈ T.sym2 ∨ s(v₁, b) ∈ T.sym2 ∨ s(b, v₂) ∈ T.sym2 := by
  -- T contains ≥ 2 of {v₁, b, v₂}
  by_cases hv1 : v₁ ∈ T
  · by_cases hv2 : v₂ ∈ T
    · left; exact sym2_mem_of_both_mem v₁ v₂ T hv1 hv2
    · -- v₁ ∈ T, v₂ ∉ T, |T ∩ B| ≥ 2 → b ∈ T
      have hb : b ∈ T := by
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
  · -- v₁ ∉ T
    by_cases hv2 : v₂ ∈ T
    · -- v₂ ∈ T, v₁ ∉ T → b ∈ T
      have hb : b ∈ T := by
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
    · -- v₁ ∉ T, v₂ ∉ T, |T ∩ B| ≥ 2 → impossible (only b left)
      exfalso
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
