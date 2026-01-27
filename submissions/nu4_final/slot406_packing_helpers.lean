/-
  slot406_packing_helpers.lean

  HEAVILY SCAFFOLDED: Break the 6-packing proof into small lemmas

  Strategy: Prove many small intersection bounds, then combine.
  Each lemma is Tier 1 (simple set arithmetic).

  TIER: 1 (collection of simple intersection lemmas)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC INTERSECTION LEMMAS (Tier 1)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two 3-element sets sharing exactly one element have intersection card ≤ 1 -/
lemma inter_single_element (A B : Finset V) (x : V)
    (hA : A.card = 3) (hB : B.card = 3)
    (hx_A : x ∈ A) (hx_B : x ∈ B)
    (h_only : ∀ y, y ∈ A → y ∈ B → y = x) :
    (A ∩ B).card ≤ 1 := by
  have hsub : A ∩ B ⊆ {x} := by
    intro y hy
    simp only [mem_inter] at hy
    simp only [mem_singleton]
    exact h_only y hy.1 hy.2
  calc (A ∩ B).card ≤ ({x} : Finset V).card := card_le_card hsub
    _ = 1 := card_singleton x

/-- Disjoint sets have intersection card 0 ≤ 1 -/
lemma inter_disjoint (A B : Finset V) (h : Disjoint A B) :
    (A ∩ B).card ≤ 1 := by
  rw [disjoint_iff_inter_eq_empty] at h
  rw [h]
  simp

/-- If x ∈ A, x ∉ B, y ∈ A, y ∉ B, z ∈ A, z ∉ B, then A ∩ B = ∅ -/
lemma inter_empty_of_all_not_mem (A B : Finset V) (x y z : V)
    (hA : A = {x, y, z})
    (hx : x ∉ B) (hy : y ∉ B) (hz : z ∉ B) :
    A ∩ B = ∅ := by
  ext w
  simp only [mem_inter, not_mem_empty, iff_false, not_and]
  intro hw_A
  rw [hA] at hw_A
  simp only [mem_insert, mem_singleton] at hw_A
  rcases hw_A with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact hz

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 SPECIFIC INTERSECTION BOUNDS
-- ══════════════════════════════════════════════════════════════════════════════

/-- T₁ = {v₁, a₂, w₁} and T₂ = {v₁, a₃, w₂} share only v₁ -/
lemma T1_T2_share_v1 (v₁ a₂ a₃ w₁ w₂ : V) (T₁ T₂ : Finset V)
    (hT1 : T₁ = {v₁, a₂, w₁}) (hT2 : T₂ = {v₁, a₃, w₂})
    (ha2_ne_v1 : a₂ ≠ v₁) (ha3_ne_v1 : a₃ ≠ v₁)
    (hw1_ne_v1 : w₁ ≠ v₁) (hw2_ne_v1 : w₂ ≠ v₁)
    (ha2_ne_a3 : a₂ ≠ a₃) (ha2_ne_w2 : a₂ ≠ w₂)
    (hw1_ne_a3 : w₁ ≠ a₃) (hw1_ne_w2 : w₁ ≠ w₂) :
    (T₁ ∩ T₂).card ≤ 1 := by
  apply inter_single_element T₁ T₂ v₁
  · rw [hT1]; simp [ha2_ne_v1.symm, hw1_ne_v1.symm]
  · rw [hT2]; simp [ha3_ne_v1.symm, hw2_ne_v1.symm]
  · rw [hT1]; simp
  · rw [hT2]; simp
  · intro y hy1 hy2
    rw [hT1] at hy1
    rw [hT2] at hy2
    simp only [mem_insert, mem_singleton] at hy1 hy2
    rcases hy1 with rfl | rfl | rfl
    · rfl
    · -- y = a₂, y ∈ T₂
      rcases hy2 with rfl | rfl | rfl
      · exact absurd rfl ha2_ne_v1
      · exact absurd rfl ha2_ne_a3
      · exact absurd rfl ha2_ne_w2
    · -- y = w₁, y ∈ T₂
      rcases hy2 with rfl | rfl | rfl
      · exact absurd rfl hw1_ne_v1
      · exact absurd rfl hw1_ne_a3
      · exact absurd rfl hw1_ne_w2

/-- T₁ = {v₁, a₂, w₁} and T₃ = {a₂, a₃, w₃} share only a₂ -/
lemma T1_T3_share_a2 (v₁ a₂ a₃ w₁ w₃ : V) (T₁ T₃ : Finset V)
    (hT1 : T₁ = {v₁, a₂, w₁}) (hT3 : T₃ = {a₂, a₃, w₃})
    (hv1_ne_a2 : v₁ ≠ a₂) (hv1_ne_a3 : v₁ ≠ a₃) (hv1_ne_w3 : v₁ ≠ w₃)
    (hw1_ne_a2 : w₁ ≠ a₂) (hw1_ne_a3 : w₁ ≠ a₃) (hw1_ne_w3 : w₁ ≠ w₃) :
    (T₁ ∩ T₃).card ≤ 1 := by
  apply inter_single_element T₁ T₃ a₂
  · rw [hT1]; simp [hv1_ne_a2, hw1_ne_a2]
  · rw [hT3]; simp
  · rw [hT1]; simp
  · rw [hT3]; simp
  · intro y hy1 hy3
    rw [hT1] at hy1
    rw [hT3] at hy3
    simp only [mem_insert, mem_singleton] at hy1 hy3
    rcases hy1 with rfl | rfl | rfl
    · rcases hy3 with rfl | rfl | rfl
      · exact absurd rfl hv1_ne_a2
      · exact absurd rfl hv1_ne_a3
      · exact absurd rfl hv1_ne_w3
    · rfl
    · rcases hy3 with rfl | rfl | rfl
      · exact absurd rfl hw1_ne_a2
      · exact absurd rfl hw1_ne_a3
      · exact absurd rfl hw1_ne_w3

/-- T₂ = {v₁, a₃, w₂} and T₃ = {a₂, a₃, w₃} share only a₃ -/
lemma T2_T3_share_a3 (v₁ a₂ a₃ w₂ w₃ : V) (T₂ T₃ : Finset V)
    (hT2 : T₂ = {v₁, a₃, w₂}) (hT3 : T₃ = {a₂, a₃, w₃})
    (hv1_ne_a2 : v₁ ≠ a₂) (hv1_ne_a3 : v₁ ≠ a₃) (hv1_ne_w3 : v₁ ≠ w₃)
    (hw2_ne_a2 : w₂ ≠ a₂) (hw2_ne_a3 : w₂ ≠ a₃) (hw2_ne_w3 : w₂ ≠ w₃) :
    (T₂ ∩ T₃).card ≤ 1 := by
  apply inter_single_element T₂ T₃ a₃
  · rw [hT2]; simp [hv1_ne_a3, hw2_ne_a3]
  · rw [hT3]; simp
  · rw [hT2]; simp
  · rw [hT3]; simp
  · intro y hy2 hy3
    rw [hT2] at hy2
    rw [hT3] at hy3
    simp only [mem_insert, mem_singleton] at hy2 hy3
    rcases hy2 with rfl | rfl | rfl
    · rcases hy3 with rfl | rfl | rfl
      · exact absurd rfl hv1_ne_a2
      · exact absurd rfl hv1_ne_a3
      · exact absurd rfl hv1_ne_w3
    · rfl
    · rcases hy3 with rfl | rfl | rfl
      · exact absurd rfl hw2_ne_a2
      · exact absurd rfl hw2_ne_a3
      · exact absurd rfl hw2_ne_w3

/-- T₁ = {v₁, a₂, w₁} and B = {v₁, v₂, b₃} share only v₁ -/
lemma T1_B_share_v1 (v₁ v₂ a₂ b₃ w₁ : V) (T₁ B : Finset V)
    (hT1 : T₁ = {v₁, a₂, w₁}) (hB : B = {v₁, v₂, b₃})
    (ha2_ne_v1 : a₂ ≠ v₁) (ha2_ne_v2 : a₂ ≠ v₂) (ha2_ne_b3 : a₂ ≠ b₃)
    (hw1_ne_v1 : w₁ ≠ v₁) (hw1_ne_v2 : w₁ ≠ v₂) (hw1_ne_b3 : w₁ ≠ b₃) :
    (T₁ ∩ B).card ≤ 1 := by
  apply inter_single_element T₁ B v₁
  · rw [hT1]; simp [ha2_ne_v1.symm, hw1_ne_v1.symm]
  · rw [hB]; simp
  · rw [hT1]; simp
  · rw [hB]; simp
  · intro y hy1 hyB
    rw [hT1] at hy1
    rw [hB] at hyB
    simp only [mem_insert, mem_singleton] at hy1 hyB
    rcases hy1 with rfl | rfl | rfl
    · rfl
    · rcases hyB with rfl | rfl | rfl
      · exact absurd rfl ha2_ne_v1
      · exact absurd rfl ha2_ne_v2
      · exact absurd rfl ha2_ne_b3
    · rcases hyB with rfl | rfl | rfl
      · exact absurd rfl hw1_ne_v1
      · exact absurd rfl hw1_ne_v2
      · exact absurd rfl hw1_ne_b3

/-- T₃ = {a₂, a₃, w₃} and B = {v₁, v₂, b₃} are disjoint -/
lemma T3_B_disjoint (v₁ v₂ a₂ a₃ b₃ w₃ : V) (T₃ B : Finset V)
    (hT3 : T₃ = {a₂, a₃, w₃}) (hB : B = {v₁, v₂, b₃})
    (ha2_ne_v1 : a₂ ≠ v₁) (ha2_ne_v2 : a₂ ≠ v₂) (ha2_ne_b3 : a₂ ≠ b₃)
    (ha3_ne_v1 : a₃ ≠ v₁) (ha3_ne_v2 : a₃ ≠ v₂) (ha3_ne_b3 : a₃ ≠ b₃)
    (hw3_ne_v1 : w₃ ≠ v₁) (hw3_ne_v2 : w₃ ≠ v₂) (hw3_ne_b3 : w₃ ≠ b₃) :
    (T₃ ∩ B).card ≤ 1 := by
  have h : T₃ ∩ B = ∅ := inter_empty_of_all_not_mem T₃ B a₂ a₃ w₃ hT3
    (by rw [hB]; simp [ha2_ne_v1, ha2_ne_v2, ha2_ne_b3])
    (by rw [hB]; simp [ha3_ne_v1, ha3_ne_v2, ha3_ne_b3])
    (by rw [hB]; simp [hw3_ne_v1, hw3_ne_v2, hw3_ne_b3])
  rw [h]
  simp

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING DEFINITION AND 6-PACKING LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- If we have 6 pairwise edge-disjoint triangles but ν = 4, contradiction -/
theorem six_triangles_contradict_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T₁ T₂ T₃ B C D : Finset V)
    (hT1 : T₁ ∈ G.cliqueFinset 3) (hT2 : T₂ ∈ G.cliqueFinset 3)
    (hT3 : T₃ ∈ G.cliqueFinset 3) (hB : B ∈ G.cliqueFinset 3)
    (hC : C ∈ G.cliqueFinset 3) (hD : D ∈ G.cliqueFinset 3)
    (h_distinct : T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₁ ≠ B ∧ T₁ ≠ C ∧ T₁ ≠ D ∧
                  T₂ ≠ T₃ ∧ T₂ ≠ B ∧ T₂ ≠ C ∧ T₂ ≠ D ∧
                  T₃ ≠ B ∧ T₃ ≠ C ∧ T₃ ≠ D ∧
                  B ≠ C ∧ B ≠ D ∧ C ≠ D)
    (h12 : (T₁ ∩ T₂).card ≤ 1) (h13 : (T₁ ∩ T₃).card ≤ 1)
    (h1B : (T₁ ∩ B).card ≤ 1) (h1C : (T₁ ∩ C).card ≤ 1) (h1D : (T₁ ∩ D).card ≤ 1)
    (h23 : (T₂ ∩ T₃).card ≤ 1)
    (h2B : (T₂ ∩ B).card ≤ 1) (h2C : (T₂ ∩ C).card ≤ 1) (h2D : (T₂ ∩ D).card ≤ 1)
    (h3B : (T₃ ∩ B).card ≤ 1) (h3C : (T₃ ∩ C).card ≤ 1) (h3D : (T₃ ∩ D).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) (hBD : (B ∩ D).card ≤ 1) (hCD : (C ∩ D).card ≤ 1)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4) :
    False := by
  -- The set {T₁, T₂, T₃, B, C, D} is a 6-packing
  let S : Finset (Finset V) := {T₁, T₂, T₃, B, C, D}
  have hS_packing : isTrianglePacking G S := by
    constructor
    · -- All in G.cliqueFinset 3
      intro X hX
      simp only [S, mem_insert, mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · -- Pairwise edge-disjoint
      intro X hX Y hY hXY
      simp only [S, mem_insert, mem_singleton, mem_coe] at hX hY
      -- Case analysis on which pair
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hY with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hXY | assumption | (rw [inter_comm]; assumption)
  have hS_card : S.card = 6 := by
    simp only [S]
    rw [card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem,
        card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
    · simp [h_distinct.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    · simp [h_distinct.2.2.2.2.2.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    · simp [h_distinct.2.2.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.2.2.2.1]
    · simp [h_distinct.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.1]
    · simp [h_distinct.1, h_distinct.2.1, h_distinct.2.2.1, h_distinct.2.2.2.1, h_distinct.2.2.2.2.1]
  have h_bound := hNu4 S hS_packing
  omega

end
