-- Lean 4 Code Skeleton for 6-Packing Contradiction Proof
-- This file provides the complete structure with tactic outlines

import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Assuming these definitions exist from previous files:
-- - isTrianglePacking
-- - type1Exists, type2Exists, type3Exists
-- - externalsWithEdge

/-
PROOF STRUCTURE FOR 6-PACKING CONTRADICTION

Theorem: For any packing M of size ≤ 4, we cannot have all three external types
relative to some triangle E.

Main theorem statement:
-/

theorem not_all_three_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    ¬(type1Exists G a b c ∧ type2Exists G a b c ∧ type3Exists G a b c) := by

  -- ========================================================================
  -- STEP 1: ASSUME ALL THREE TYPES EXIST
  -- ========================================================================
  intro ⟨h1, h2, h3⟩

  -- ========================================================================
  -- STEP 2: EXTRACT WITNESSES FROM NONEMPTY
  -- ========================================================================

  -- Extract Type 1 witness: T₁ shares edge {a,b}, missing c
  unfold type1Exists at h1
  obtain ⟨T₁, hT₁⟩ := h1
  simp only [externalsWithEdge, Finset.mem_filter] at hT₁
  obtain ⟨hT₁_clique, hT₁_ne_E, hT₁_ab, hT₁_c_not⟩ := hT₁
  have hT₁_a : a ∈ T₁ := hT₁_ab.1
  have hT₁_b : b ∈ T₁ := hT₁_ab.2

  -- Extract Type 2 witness: T₂ shares edge {b,c}, missing a
  unfold type2Exists at h2
  obtain ⟨T₂, hT₂⟩ := h2
  simp only [externalsWithEdge, Finset.mem_filter] at hT₂
  obtain ⟨hT₂_clique, hT₂_ne_E, hT₂_bc, hT₂_a_not⟩ := hT₂
  have hT₂_b : b ∈ T₂ := hT₂_bc.1
  have hT₂_c : c ∈ T₂ := hT₂_bc.2

  -- Extract Type 3 witness: T₃ shares edge {c,a}, missing b
  unfold type3Exists at h3
  obtain ⟨T₃, hT₃⟩ := h3
  simp only [externalsWithEdge, Finset.mem_filter] at hT₃
  obtain ⟨hT₃_clique, hT₃_ne_E, hT₃_ca, hT₃_b_not⟩ := hT₃
  have hT₃_c : c ∈ T₃ := hT₃_ca.1
  have hT₃_a : a ∈ T₃ := hT₃_ca.2

  -- ========================================================================
  -- STEP 3: DEFINE CANDIDATE 6-PACKING
  -- ========================================================================

  set S : Finset (Finset V) := {T₁, T₂, T₃, B, C, D}

  -- ========================================================================
  -- STEP 4: PROVE PAIRWISE INTERSECTIONS ≤ 1 (15 CASES)
  -- ========================================================================

  -- Within external triangles (9 cases among T₁, T₂, T₃)
  have hT₁T₂_inter : (T₁ ∩ T₂).card ≤ 1 := by
    -- T₁ contains {a,b}, T₂ contains {b,c}
    -- They share at most vertex b
    -- But both are size 3, and:
    -- - T₁ \ E = {x} for some x ∉ {a,b,c}
    -- - T₂ \ E = {y} for some y ∉ {a,b,c}, x ≠ y
    -- So T₁ = {a,b,x}, T₂ = {b,c,y} with x ≠ y
    -- Therefore T₁ ∩ T₂ ⊆ {b}, so |T₁ ∩ T₂| ≤ 1
    by_contra h
    push_neg at h
    -- |T₁ ∩ T₂| ≥ 2
    -- But we can extract the third vertices of each triangle
    -- and show they must be different
    omega

  have hT₁T₃_inter : (T₁ ∩ T₃).card ≤ 1 := by
    -- T₁ contains {a,b}, T₃ contains {a,c}
    -- They share at most vertex a
    by_contra h
    push_neg at h
    omega

  have hT₂T₃_inter : (T₂ ∩ T₃).card ≤ 1 := by
    -- T₂ contains {b,c}, T₃ contains {a,c}
    -- They share at most vertex c
    by_contra h
    push_neg at h
    omega

  -- T_i vs packing elements (6 cases)
  have hT₁B_inter : (T₁ ∩ B).card ≤ 1 := by omega
  have hT₁C_inter : (T₁ ∩ C).card ≤ 1 := by omega
  have hT₁D_inter : (T₁ ∩ D).card ≤ 1 := by omega

  have hT₂B_inter : (T₂ ∩ B).card ≤ 1 := by omega
  have hT₂C_inter : (T₂ ∩ C).card ≤ 1 := by omega
  have hT₂D_inter : (T₂ ∩ D).card ≤ 1 := by omega

  have hT₃B_inter : (T₃ ∩ B).card ≤ 1 := by omega
  have hT₃C_inter : (T₃ ∩ C).card ≤ 1 := by omega
  have hT₃D_inter : (T₃ ∩ D).card ≤ 1 := by omega

  -- Original packing pairs (already known to satisfy ≤ 1)
  have hBC_inter : (B ∩ C).card ≤ 1 := by
    have : Set.Pairwise (M : Set (Finset V)) (fun t t' => (t ∩ t').card ≤ 1) :=
      hM.2
    simp [Set.Pairwise] at this
    exact this B hB C hC hBC

  have hBD_inter : (B ∩ D).card ≤ 1 := by
    have : Set.Pairwise (M : Set (Finset V)) (fun t t' => (t ∩ t').card ≤ 1) :=
      hM.2
    simp [Set.Pairwise] at this
    exact this B hB D hD hBD

  have hCD_inter : (C ∩ D).card ≤ 1 := by
    have : Set.Pairwise (M : Set (Finset V)) (fun t t' => (t ∩ t').card ≤ 1) :=
      hM.2
    simp [Set.Pairwise] at this
    exact this C hC D hD hCD

  -- ========================================================================
  -- STEP 5: VERIFY ALL ELEMENTS ARE TRIANGLES
  -- ========================================================================

  have hS_all_triangles : ∀ t ∈ S, t ∈ G.cliqueFinset 3 := by
    intro t ht
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with (rfl | rfl | rfl | rfl | rfl | rfl)
    · -- T₁ is a triangle
      exact hT₁_clique
    · -- T₂ is a triangle
      exact hT₂_clique
    · -- T₃ is a triangle
      exact hT₃_clique
    · -- B is a triangle (in M)
      exact hM.1 hB
    · -- C is a triangle (in M)
      exact hM.1 hC
    · -- D is a triangle (in M)
      exact hM.1 hD

  -- ========================================================================
  -- STEP 6: PROVE S IS A TRIANGLE PACKING
  -- ========================================================================

  have hS_packing : isTrianglePacking G S := by
    constructor
    · -- S ⊆ G.cliqueFinset 3
      intro t ht
      exact hS_all_triangles t ht
    · -- Pairwise intersections ≤ 1
      simp only [Set.Pairwise]
      intro t ht t' ht' hne
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht ht'
      -- Case split on which pair (t, t') is
      rcases ht with (rfl | ht)
      · -- t = T₁
        rcases ht' with (rfl | ht')
        · exact absurd rfl hne
        · rcases ht' with (rfl | ht')
          · exact hT₁T₂_inter
          · rcases ht' with (rfl | ht')
            · exact hT₁T₃_inter
            · rcases ht' with (rfl | ht')
              · exact hT₁B_inter
              · rcases ht' with (rfl | ht')
                · exact hT₁C_inter
                · simp at ht'; rw [ht'] at *
                  exact hT₁D_inter
      · -- t ≠ T₁
        rcases ht with (rfl | ht)
        · -- t = T₂
          rcases ht' with (rfl | ht')
          · exact absurd rfl hne
          · rcases ht' with (rfl | ht')
            · exact hT₂T₁_inter.symm
            · -- Continue pattern for all remaining pairs
              sorry
        · sorry  -- Continue pattern recursively

  -- ========================================================================
  -- STEP 7: PROVE ALL SIX ELEMENTS ARE DISTINCT
  -- ========================================================================

  -- T₁ ≠ T₂ (different external vertices)
  have hT₁_ne_T₂ : T₁ ≠ T₂ := by
    intro h
    rw [h] at hT₁_c_not
    exact hT₁_c_not hT₂_c

  -- T₁ ≠ T₃
  have hT₁_ne_T₃ : T₁ ≠ T₃ := by
    intro h
    rw [h] at hT₁_b
    exact hT₃_b_not hT₁_b

  -- T₂ ≠ T₃
  have hT₂_ne_T₃ : T₂ ≠ T₃ := by
    intro h
    rw [h] at hT₂_a_not
    exact hT₂_a_not hT₃_a

  -- T₁ ≠ B, T₁ ≠ C, T₁ ≠ D
  have hT₁_ne_B : T₁ ≠ B := by
    intro h
    rw [h] at hT₁_ne_E
    exact hT₁_ne_E hB_ne

  have hT₁_ne_C : T₁ ≠ C := by
    intro h
    rw [h] at hT₁_ne_E
    exact hT₁_ne_E hC_ne

  have hT₁_ne_D : T₁ ≠ D := by
    intro h
    rw [h] at hT₁_ne_E
    exact hT₁_ne_E hD_ne

  -- Similarly for T₂ and T₃
  have hT₂_ne_B : T₂ ≠ B := by
    intro h
    rw [h] at hT₂_ne_E
    exact hT₂_ne_E hB_ne

  have hT₂_ne_C : T₂ ≠ C := by
    intro h
    rw [h] at hT₂_ne_E
    exact hT₂_ne_E hC_ne

  have hT₂_ne_D : T₂ ≠ D := by
    intro h
    rw [h] at hT₂_ne_E
    exact hT₂_ne_E hD_ne

  have hT₃_ne_B : T₃ ≠ B := by
    intro h
    rw [h] at hT₃_ne_E
    exact hT₃_ne_E hB_ne

  have hT₃_ne_C : T₃ ≠ C := by
    intro h
    rw [h] at hT₃_ne_E
    exact hT₃_ne_E hC_ne

  have hT₃_ne_D : T₃ ≠ D := by
    intro h
    rw [h] at hT₃_ne_E
    exact hT₃_ne_E hD_ne

  -- ========================================================================
  -- STEP 8: CALCULATE CARDINALITY OF S
  -- ========================================================================

  have hS_card : S.card = 6 := by
    simp only [S, Finset.card_insert_of_notMem]
    simp only [hT₁_ne_T₂, hT₁_ne_T₃, hT₁_ne_B, hT₁_ne_C, hT₁_ne_D,
               hT₂_ne_T₃, hT₂_ne_B, hT₂_ne_C, hT₂_ne_D,
               hT₃_ne_B, hT₃_ne_C, hT₃_ne_D,
               hBC, hBD, hCD]
    simp only [Finset.card_singleton]
    norm_num

  -- ========================================================================
  -- STEP 9: APPLY hNu4 TO GET CONTRADICTION
  -- ========================================================================

  -- S is a triangle packing with 6 elements
  have h_max_four : S.card ≤ 4 := hNu4 S hS_packing

  -- But S.card = 6
  rw [hS_card] at h_max_four

  -- 6 ≤ 4 is false
  omega

end

-- ============================================================================
-- HELPER LEMMAS (if needed)
-- ============================================================================

/-
If you need to extract structure about external triangles:

lemma external_triangle_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) (T : Finset V)
    (hT : T ∈ externalsWithEdge G a b c) :
    T.card = 3 ∧ a ∈ T ∧ b ∈ T ∧ c ∉ T ∧ T ≠ {a, b, c} ∧ T ∈ G.cliqueFinset 3 := by
  simp only [externalsWithEdge, Finset.mem_filter] at hT
  obtain ⟨hclique, hne_E, hab, hc⟩ := hT
  simp only [SimpleGraph.cliqueFinset] at hclique
  exact ⟨hclique.2.2, hab.1, hab.2, hc, hne_E, ⟨hclique.1, hclique.2⟩⟩
-/

