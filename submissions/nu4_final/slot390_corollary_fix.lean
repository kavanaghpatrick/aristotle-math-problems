/-
  slot390_corollary_fix.lean

  Tuza ν=4 PATH_4: Fix trivial sorry in interior corollary

  FROM 3-AGENT DEBATE CONSENSUS (Round 2):
  The sorry at T = B is trivial because v₁ ∈ B by PATH_4 structure.
  We should handle T = B BEFORE trying to prove T ∉ M.

  PROOF SKETCH:
  1. If T = B, then v₁ ∈ T (since v₁ ∈ B by definition)
  2. If T ≠ B and T ∈ M, this violates packing (T shares ≥2 with B)
  3. If T ∉ M, apply the main theorem interior_external_contains_shared

  TIER: 1 (Simple case restructuring)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot389)
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
-- PROVEN SCAFFOLDING (from slot389 Aristotle output)
-- ══════════════════════════════════════════════════════════════════════════════

/-- In PATH_4, interior element B has exactly 3 vertices -/
lemma interior_card_three (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hM : isTrianglePacking G M) :
    B.card = 3 := by
  have hB : B ∈ M := by rw [hpath.1]; simp
  have := hM.1 hB
  exact (G.mem_cliqueFinset_iff.mp this).2

/-- Interior element B in PATH_4 has form {v₁, v₂, b₃} where v₁, v₂ are shared vertices -/
lemma interior_structure (A B C : Finset V)
    (hAB : (A ∩ B).card = 1) (hBC : (B ∩ C).card = 1)
    (hAC : (A ∩ C).card = 0)
    (hB_card : B.card = 3)
    (v₁ : V) (hv₁ : A ∩ B = {v₁})
    (v₂ : V) (hv₂ : B ∩ C = {v₂}) :
    ∃ b₃, b₃ ∉ A ∧ b₃ ∉ C ∧ b₃ ≠ v₁ ∧ b₃ ≠ v₂ ∧ B = {v₁, v₂, b₃} := by
  have hv₁_in_B : v₁ ∈ B := by
    have : v₁ ∈ A ∩ B := by rw [hv₁]; exact mem_singleton_self v₁
    exact mem_of_mem_inter_right this
  have hv₂_in_B : v₂ ∈ B := by
    have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
    exact mem_of_mem_inter_left this
  have hv₁_ne_v₂ : v₁ ≠ v₂ := by
    intro heq
    have hv₁_in_A : v₁ ∈ A := by
      have : v₁ ∈ A ∩ B := by rw [hv₁]; exact mem_singleton_self v₁
      exact mem_of_mem_inter_left this
    have hv₂_in_C : v₂ ∈ C := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
      exact mem_of_mem_inter_right this
    rw [heq] at hv₁_in_A
    have : v₂ ∈ A ∩ C := mem_inter.mpr ⟨hv₁_in_A, hv₂_in_C⟩
    rw [hAC] at this
    exact not_mem_empty v₂ this
  have hv₁v₂_card : ({v₁, v₂} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem, card_singleton]
    simp [hv₁_ne_v₂]
  have hB_diff_nonempty : (B \ {v₁, v₂}).Nonempty := by
    rw [← card_pos]
    have : B.card = ({v₁, v₂} : Finset V).card + (B \ {v₁, v₂}).card := by
      have hsub : {v₁, v₂} ⊆ B := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      rw [← card_sdiff hsub, add_comm, Nat.sub_add_cancel (card_le_card hsub)]
    rw [hB_card, hv₁v₂_card] at this
    omega
  obtain ⟨b₃, hb₃⟩ := hB_diff_nonempty
  simp at hb₃
  obtain ⟨hb₃_in_B, hb₃_ne_v₁, hb₃_ne_v₂⟩ := hb₃
  use b₃
  refine ⟨?_, ?_, hb₃_ne_v₁, hb₃_ne_v₂, ?_⟩
  · intro hb₃_in_A
    have : b₃ ∈ A ∩ B := mem_inter.mpr ⟨hb₃_in_A, hb₃_in_B⟩
    rw [hv₁] at this; simp at this; exact hb₃_ne_v₁ this
  · intro hb₃_in_C
    have : b₃ ∈ B ∩ C := mem_inter.mpr ⟨hb₃_in_B, hb₃_in_C⟩
    rw [hv₂] at this; simp at this; exact hb₃_ne_v₂ this
  · ext x; simp
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · have : x ∈ A ∩ B := mem_inter.mpr ⟨hxA, hx⟩
        rw [hv₁] at this; simp at this; left; exact this
      · by_cases hxC : x ∈ C
        · have : x ∈ B ∩ C := mem_inter.mpr ⟨hx, hxC⟩
          rw [hv₂] at this; simp at this; right; left; exact this
        · right; right
          have hsub : {v₁, v₂, x} ⊆ B := by
            intro w hw; simp at hw
            rcases hw with rfl | rfl | rfl <;> [exact hv₁_in_B; exact hv₂_in_B; exact hx]
          have hcard : ({v₁, v₂, x} : Finset V).card = 3 := by
            rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
            · simp [hv₁_ne_v₂]
            · simp; intro heq; rw [heq] at hxA
              have : v₁ ∈ A := by
                have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
                exact mem_of_mem_inter_left this
              exact hxA this
          have heq := eq_of_subset_of_card_le hsub (by rw [hB_card, hcard])
          have hb₃_in_set : b₃ ∈ ({v₁, v₂, x} : Finset V) := by rw [← heq]; exact hb₃_in_B
          simp at hb₃_in_set
          rcases hb₃_in_set with rfl | rfl | rfl
          · exact absurd rfl hb₃_ne_v₁
          · exact absurd rfl hb₃_ne_v₂
          · rfl
    · intro hx
      rcases hx with rfl | rfl | rfl <;> [exact hv₁_in_B; exact hv₂_in_B; exact hb₃_in_B]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM (PROVEN by Aristotle in slot389)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: Any external triangle sharing edge with interior element B
    must contain one of B's shared vertices -/
theorem interior_external_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₁ v₂ : V) (hv₁ : A ∩ B = {v₁}) (hv₂ : B ∩ C = {v₂})
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_ext : T ∉ M)
    (hT_share : (T ∩ B).card ≥ 2) :
    v₁ ∈ T ∨ v₂ ∈ T := by
  have hB_card : B.card = 3 := interior_card_three M A B C D hpath G hM
  have hAC : (A ∩ C).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.1
  have hAB : (A ∩ B).card = 1 := hpath.2.2.2.2.2.2.2.1
  have hBC : (B ∩ C).card = 1 := hpath.2.2.2.2.2.2.2.2.1
  obtain ⟨b₃, _, _, hb₃_ne_v₁, hb₃_ne_v₂, hB_eq⟩ :=
    interior_structure A B C hAB hBC hAC hB_card v₁ hv₁ v₂ hv₂
  have hv₁_ne_v₂ : v₁ ≠ v₂ := by
    intro heq
    have hv₁_in_A : v₁ ∈ A := by
      have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
      exact mem_of_mem_inter_left this
    have hv₂_in_C : v₂ ∈ C := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
      exact mem_of_mem_inter_right this
    rw [heq] at hv₁_in_A
    have : v₂ ∈ A ∩ C := mem_inter.mpr ⟨hv₁_in_A, hv₂_in_C⟩
    rw [Finset.card_eq_zero.mp hAC] at this
    exact not_mem_empty _ this
  rw [hB_eq] at hT_share
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hT_share
  have hx_in_T : x ∈ T := mem_of_mem_inter_left hx
  have hy_in_T : y ∈ T := mem_of_mem_inter_left hy
  have hx_in_B : x ∈ ({v₁, v₂, b₃} : Finset V) := mem_of_mem_inter_right hx
  have hy_in_B : y ∈ ({v₁, v₂, b₃} : Finset V) := mem_of_mem_inter_right hy
  simp at hx_in_B hy_in_B
  rcases hx_in_B with rfl | rfl | rfl
  · left; exact hx_in_T
  · right; exact hx_in_T
  · rcases hy_in_B with rfl | rfl | rfl
    · left; exact hy_in_T
    · right; exact hy_in_T
    · exact absurd rfl hxy

-- ══════════════════════════════════════════════════════════════════════════════
-- FIXED COROLLARY: Handle T = B case BEFORE proving T ∉ M
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (FIX):
1. First check if T = B
2. If T = B: v₁ ∈ B directly (by PATH_4 structure), so v₁ ∈ T. Done.
3. If T ≠ B and T ∈ M: violates packing (T shares ≥2 vertices with B)
4. If T ∉ M: apply main theorem
-/

/-- v₁ is in B (helper for the fix) -/
lemma v₁_mem_B (A B : Finset V) (v₁ : V) (hv₁ : A ∩ B = {v₁}) : v₁ ∈ B := by
  have : v₁ ∈ A ∩ B := by rw [hv₁]; exact mem_singleton_self v₁
  exact mem_of_mem_inter_right this

/-- Corollary: S_B externals are covered by edges containing v₁ or v₂ -/
theorem interior_S_covered_by_shared_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₁ v₂ : V) (hv₁ : A ∩ B = {v₁}) (hv₂ : B ∩ C = {v₂}) :
    ∀ T ∈ S_e G M B, v₁ ∈ T ∨ v₂ ∈ T := by
  intro T hT
  -- First: check if T = B (handle this case directly)
  by_cases hTeq : T = B
  · -- T = B case: v₁ ∈ B by PATH_4 structure, so v₁ ∈ T
    left
    rw [hTeq]
    exact v₁_mem_B A B v₁ hv₁
  · -- T ≠ B case: prove T ∉ M, then use main theorem
    have hT_tri : T ∈ G.cliqueFinset 3 := by
      simp [S_e, trianglesSharingEdge] at hT
      exact hT.1.1
    have hT_share : (T ∩ B).card ≥ 2 := by
      simp [S_e, trianglesSharingEdge] at hT
      exact hT.1.2
    have hT_not_in_M : T ∉ M := by
      intro hT_in_M
      -- T ≠ B and T ∈ M, T shares ≥2 with B violates packing
      have hpacking := hM.2
      have hB_in_M : B ∈ M := by rw [hpath.1]; simp
      specialize hpacking hT_in_M hB_in_M hTeq
      omega
    exact interior_external_contains_shared G M A B C D hpath hM v₁ v₂ hv₁ hv₂ T hT_tri hT_not_in_M hT_share

end
