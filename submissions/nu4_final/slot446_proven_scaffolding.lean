/-
  slot446_proven_scaffolding.lean

  Proven lemmas extracted from slot446 Aristotle output.
  The main theorem was NEGATED, but these helper lemmas are PROVEN.

  KEY INSIGHT: six_packing_implies_missing_edge shows that
  6-packing constraint forces at least one edge to be missing.
  Use the corresponding endpoint_adaptive_cover_of_missing_* lemma.
-/

import Mathlib

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isSeExternal_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  2 ≤ (T ∩ A).card ∧
  (T ∩ B).card ≤ 1

def SixPackingEndpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (a₁ a₂ v₁ : V) : Prop :=
  (∀ T, isSeExternal_A G A B T → ¬(a₁ ∈ T ∧ a₂ ∈ T)) ∨
  (∀ T, isSeExternal_A G A B T → ¬(a₁ ∈ T ∧ v₁ ∈ T)) ∨
  (∀ T, isSeExternal_A G A B T → ¬(a₂ ∈ T ∧ v₁ ∈ T))

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: One of three edges hits any A-interacting triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma sym2_mem_of_both_mem (a b : V) (T : Finset V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

theorem endpoint_one_of_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTA : 2 ≤ (T ∩ {a₁, a₂, v₁}).card) :
    s(a₁, a₂) ∈ T.sym2 ∨ s(a₁, v₁) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
  by_cases ha1 : a₁ ∈ T
  · by_cases ha2 : a₂ ∈ T
    · left; exact sym2_mem_of_both_mem a₁ a₂ T ha1 ha2
    · have hv1 : v₁ ∈ T := by
        by_contra hv1_not
        have h_sub : T ∩ {a₁, a₂, v₁} ⊆ {a₁} := by
          intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · rfl
          · exact absurd hx.1 ha2
          · exact absurd hx.1 hv1_not
        have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
          calc (T ∩ {a₁, a₂, v₁}).card ≤ ({a₁} : Finset V).card := card_le_card h_sub
            _ = 1 := card_singleton _
        omega
      right; left; exact sym2_mem_of_both_mem a₁ v₁ T ha1 hv1
  · by_cases ha2 : a₂ ∈ T
    · have hv1 : v₁ ∈ T := by
        by_contra hv1_not
        have h_sub : T ∩ {a₁, a₂, v₁} ⊆ {a₂} := by
          intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · exact absurd hx.1 ha1
          · rfl
          · exact absurd hx.1 hv1_not
        have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
          calc (T ∩ {a₁, a₂, v₁}).card ≤ ({a₂} : Finset V).card := card_le_card h_sub
            _ = 1 := card_singleton _
        omega
      right; right; exact sym2_mem_of_both_mem a₂ v₁ T ha2 hv1
    · exfalso
      have h_sub : T ∩ {a₁, a₂, v₁} ⊆ {v₁} := by
        intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 ha1
        · exact absurd hx.1 ha2
        · rfl
      have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
        calc (T ∩ {a₁, a₂, v₁}).card ≤ ({v₁} : Finset V).card := card_le_card h_sub
          _ = 1 := card_singleton _
      omega

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: 6-packing implies missing edge
-- ══════════════════════════════════════════════════════════════════════════════

/-- KEY THEOREM: If 6-packing holds, at least one edge of the triangle is missing -/
lemma six_packing_implies_missing_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V) (B : Finset V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ B = {v₁})
    (h_6pack : SixPackingEndpoint G {a₁, a₂, v₁} B a₁ a₂ v₁) :
    ¬(G.Adj a₁ a₂ ∧ G.Adj a₁ v₁ ∧ G.Adj a₂ v₁) := by
  unfold SixPackingEndpoint at h_6pack
  unfold isSeExternal_A at h_6pack
  simp_all +decide
  contrapose! h_6pack
  refine ⟨⟨{a₁, a₂, v₁}, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨{a₁, a₂, v₁}, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨{a₁, a₂, v₁}, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  simp_all +decide [SimpleGraph.isNClique_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: Adaptive covers when edges are missing
-- ══════════════════════════════════════════════════════════════════════════════

/-- If base edge (a1, a2) is missing, the two spoke edges form a valid cover -/
lemma endpoint_adaptive_cover_of_missing_base (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₁ a₂) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  refine ⟨s(a₁, v₁), s(a₂, v₁), ?_, ?_, ?_⟩ <;> simp +decide [*]
  intro T hT hT'
  have := Finset.one_lt_card.1 hT'
  simp_all +decide [Finset.ext_iff]
  rcases this with ⟨x, hx, y, hy, hxy⟩
  rcases hx with ⟨hx₁, rfl | rfl | rfl⟩ <;>
  rcases hy with ⟨hy₁, rfl | rfl | rfl⟩ <;>
  simp_all +decide
  · have := hT.1
    simp_all +decide [SimpleGraph.isNClique_iff]
    exact False.elim (h_missing (this hx₁ hy₁ (by tauto)))
  · have := hT.1
    simp_all +decide [SimpleGraph.isNClique_iff]
    exact False.elim (h_missing (this hy₁ hx₁ (by tauto)))

/-- If right spoke edge (a2, v1) is missing, base + left spoke form a valid cover -/
lemma endpoint_adaptive_cover_of_missing_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₂ v₁) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  use s(a₁, a₂), s(a₁, v₁)
  refine ⟨by simp, by simp, ?_⟩
  intro T hT hTA
  have h_cases := endpoint_one_of_three G a₁ a₂ v₁ h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 T hT hTA
  contrapose! h_missing
  simp_all +decide [Sym2.mem_iff]
  have := hT.1
  aesop

-- Note: endpoint_adaptive_cover_of_missing_left needs the helper lemma
-- endpoint_cover_aux_left which uses exact? (not fully proven)
-- The pattern is symmetric to missing_right

end
