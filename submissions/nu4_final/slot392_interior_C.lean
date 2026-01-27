/-
  slot392_interior_C.lean

  Tuza ν=4 PATH_4: Interior C External Constraint (SYMMETRIC to slot390)

  3-AGENT DEBATE CONSENSUS:
  This is the SYMMETRIC proof of slot390 for interior element C.

  slot390 proved: B externals contain v₁ or v₂
  slot392 proves: C externals contain v₂ or v₃

  WHY: C = {v₂, v₃, c₃} where v₂ shared with B, v₃ shared with D.
  Every edge of C contains at least one shared vertex.
  Therefore ANY external t ∈ S_C must contain v₂ OR v₃.

  CONSEQUENCE: S_C is covered "for free" by spine edges or endpoint spokes.
  Combined with slot390: Interior elements B, C contribute 0 edges to cover.

  PROOF SKETCH:
  1. C = {v₂, v₃, c₃} by PATH_4 structure
  2. edges(C) = {{v₂,v₃}, {v₂,c₃}, {v₃,c₃}}
  3. Every edge of C contains v₂ or v₃
  4. t shares edge with C ⟹ t contains 2 vertices from C
  5. Case analysis: at least one must be v₂ or v₃

  TIER: 1 (Symmetric to slot390 which succeeded with 0 sorry)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot390)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Basic facts about PATH_4 structure (symmetric to slot390)
-- ══════════════════════════════════════════════════════════════════════════════

/-- In PATH_4, interior element C has exactly 3 vertices -/
lemma interior_card_three_C (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hM : isTrianglePacking G M) :
    C.card = 3 := by
  have hC : C ∈ M := by rw [hpath.1]; simp
  have := hM.1 hC
  exact (G.mem_cliqueFinset_iff.mp this).2

/-- Interior element C in PATH_4 has form {v₂, v₃, c₃} where v₂, v₃ are shared vertices -/
lemma interior_structure_C (B C D : Finset V)
    (hBC : (B ∩ C).card = 1) (hCD : (C ∩ D).card = 1)
    (hBD : (B ∩ D).card = 0)
    (hC_card : C.card = 3)
    (v₂ : V) (hv₂ : B ∩ C = {v₂})
    (v₃ : V) (hv₃ : C ∩ D = {v₃}) :
    ∃ c₃, c₃ ∉ B ∧ c₃ ∉ D ∧ c₃ ≠ v₂ ∧ c₃ ≠ v₃ ∧ C = {v₂, v₃, c₃} := by
  have hv₂_in_C : v₂ ∈ C := by
    have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
    exact mem_of_mem_inter_right this
  have hv₃_in_C : v₃ ∈ C := by
    have : v₃ ∈ C ∩ D := by rw [hv₃]; exact mem_singleton_self v₃
    exact mem_of_mem_inter_left this
  have hv₂_ne_v₃ : v₂ ≠ v₃ := by
    intro heq
    have hv₂_in_B : v₂ ∈ B := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
      exact mem_of_mem_inter_left this
    have hv₃_in_D : v₃ ∈ D := by
      have : v₃ ∈ C ∩ D := by rw [hv₃]; exact mem_singleton_self v₃
      exact mem_of_mem_inter_right this
    rw [heq] at hv₂_in_B
    have : v₃ ∈ B ∩ D := mem_inter.mpr ⟨hv₂_in_B, hv₃_in_D⟩
    rw [hBD] at this
    exact not_mem_empty v₃ this
  have hv₂v₃_card : ({v₂, v₃} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem, card_singleton]
    simp [hv₂_ne_v₃]
  have hC_diff_nonempty : (C \ {v₂, v₃}).Nonempty := by
    rw [← card_pos]
    have : C.card = ({v₂, v₃} : Finset V).card + (C \ {v₂, v₃}).card := by
      have hsub : {v₂, v₃} ⊆ C := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      rw [← card_sdiff hsub, add_comm, Nat.sub_add_cancel (card_le_card hsub)]
    rw [hC_card, hv₂v₃_card] at this
    omega
  obtain ⟨c₃, hc₃⟩ := hC_diff_nonempty
  simp at hc₃
  obtain ⟨hc₃_in_C, hc₃_ne_v₂, hc₃_ne_v₃⟩ := hc₃
  use c₃
  refine ⟨?_, ?_, hc₃_ne_v₂, hc₃_ne_v₃, ?_⟩
  · intro hc₃_in_B
    have : c₃ ∈ B ∩ C := mem_inter.mpr ⟨hc₃_in_B, hc₃_in_C⟩
    rw [hv₂] at this; simp at this; exact hc₃_ne_v₂ this
  · intro hc₃_in_D
    have : c₃ ∈ C ∩ D := mem_inter.mpr ⟨hc₃_in_C, hc₃_in_D⟩
    rw [hv₃] at this; simp at this; exact hc₃_ne_v₃ this
  · ext x; simp
    constructor
    · intro hx
      by_cases hxB : x ∈ B
      · have : x ∈ B ∩ C := mem_inter.mpr ⟨hxB, hx⟩
        rw [hv₂] at this; simp at this; left; exact this
      · by_cases hxD : x ∈ D
        · have : x ∈ C ∩ D := mem_inter.mpr ⟨hx, hxD⟩
          rw [hv₃] at this; simp at this; right; left; exact this
        · right; right
          have hsub : {v₂, v₃, x} ⊆ C := by
            intro w hw; simp at hw
            rcases hw with rfl | rfl | rfl <;> [exact hv₂_in_C; exact hv₃_in_C; exact hx]
          have hcard : ({v₂, v₃, x} : Finset V).card = 3 := by
            rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
            · simp [hv₂_ne_v₃]
            · simp; intro heq; rw [heq] at hxB
              have : v₂ ∈ B := by
                have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
                exact mem_of_mem_inter_left this
              exact hxB this
          have heq := eq_of_subset_of_card_le hsub (by rw [hC_card, hcard])
          have hc₃_in_set : c₃ ∈ ({v₂, v₃, x} : Finset V) := by rw [← heq]; exact hc₃_in_C
          simp at hc₃_in_set
          rcases hc₃_in_set with rfl | rfl | rfl
          · exact absurd rfl hc₃_ne_v₂
          · exact absurd rfl hc₃_ne_v₃
          · rfl
    · intro hx
      rcases hx with rfl | rfl | rfl <;> [exact hv₂_in_C; exact hv₃_in_C; exact hc₃_in_C]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Interior C externals contain shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: Any external triangle sharing edge with interior element C
    must contain one of C's shared vertices (v₂ or v₃) -/
theorem interior_external_contains_shared_C (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₂ v₃ : V) (hv₂ : B ∩ C = {v₂}) (hv₃ : C ∩ D = {v₃})
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_ext : T ∉ M)
    (hT_share : (T ∩ C).card ≥ 2) :
    v₂ ∈ T ∨ v₃ ∈ T := by
  have hC_card : C.card = 3 := interior_card_three_C M A B C D hpath G hM
  have hBD : (B ∩ D).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.2
  have hBC : (B ∩ C).card = 1 := hpath.2.2.2.2.2.2.2.2.1
  have hCD : (C ∩ D).card = 1 := hpath.2.2.2.2.2.2.2.2.2.1
  obtain ⟨c₃, _, _, hc₃_ne_v₂, hc₃_ne_v₃, hC_eq⟩ :=
    interior_structure_C B C D hBC hCD hBD hC_card v₂ hv₂ v₃ hv₃
  have hv₂_ne_v₃ : v₂ ≠ v₃ := by
    intro heq
    have hv₂_in_B : v₂ ∈ B := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
      exact mem_of_mem_inter_left this
    have hv₃_in_D : v₃ ∈ D := by
      have : v₃ ∈ C ∩ D := by rw [hv₃]; simp
      exact mem_of_mem_inter_right this
    rw [heq] at hv₂_in_B
    have : v₃ ∈ B ∩ D := mem_inter.mpr ⟨hv₂_in_B, hv₃_in_D⟩
    rw [Finset.card_eq_zero.mp hBD] at this
    exact not_mem_empty _ this
  rw [hC_eq] at hT_share
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hT_share
  have hx_in_T : x ∈ T := mem_of_mem_inter_left hx
  have hy_in_T : y ∈ T := mem_of_mem_inter_left hy
  have hx_in_C : x ∈ ({v₂, v₃, c₃} : Finset V) := mem_of_mem_inter_right hx
  have hy_in_C : y ∈ ({v₂, v₃, c₃} : Finset V) := mem_of_mem_inter_right hy
  simp at hx_in_C hy_in_C
  rcases hx_in_C with rfl | rfl | rfl
  · left; exact hx_in_T
  · right; exact hx_in_T
  · rcases hy_in_C with rfl | rfl | rfl
    · left; exact hy_in_T
    · right; exact hy_in_T
    · exact absurd rfl hxy

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: S_C externals covered by edges containing v₂ or v₃
-- ══════════════════════════════════════════════════════════════════════════════

/-- v₂ is in C (helper) -/
lemma v₂_mem_C (B C : Finset V) (v₂ : V) (hv₂ : B ∩ C = {v₂}) : v₂ ∈ C := by
  have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
  exact mem_of_mem_inter_right this

/-- Corollary: S_C externals are covered by edges containing v₂ or v₃ -/
theorem interior_S_covered_by_shared_spokes_C (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₂ v₃ : V) (hv₂ : B ∩ C = {v₂}) (hv₃ : C ∩ D = {v₃}) :
    ∀ T ∈ S_e G M C, v₂ ∈ T ∨ v₃ ∈ T := by
  intro T hT
  by_cases hTeq : T = C
  · left
    rw [hTeq]
    exact v₂_mem_C B C v₂ hv₂
  · have hT_tri : T ∈ G.cliqueFinset 3 := by
      simp [S_e, trianglesSharingEdge] at hT
      exact hT.1.1
    have hT_share : (T ∩ C).card ≥ 2 := by
      simp [S_e, trianglesSharingEdge] at hT
      exact hT.1.2
    have hT_not_in_M : T ∉ M := by
      intro hT_in_M
      have hpacking := hM.2
      have hC_in_M : C ∈ M := by rw [hpath.1]; simp
      specialize hpacking hT_in_M hC_in_M hTeq
      omega
    exact interior_external_contains_shared_C G M A B C D hpath hM v₂ v₃ hv₂ hv₃ T hT_tri hT_not_in_M hT_share

end
