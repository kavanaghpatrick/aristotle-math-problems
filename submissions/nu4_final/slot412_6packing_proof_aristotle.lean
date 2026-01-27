/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a1cfae0f-f8a4-4279-bd6d-cae77bc5ed0f
-/

/-
  slot412_6packing_proof.lean

  CRITICAL LEMMA: All 3 external types CANNOT coexist for any M-element

  This proves the key assumption used by slot409/slot410.

  INSIGHT: External triangles T in S_e satisfy:
  1. T shares edge with e (intersection ≥ 2)
  2. T is edge-disjoint from OTHER M-elements (intersection ≤ 1)

  If all 3 edge-types of E have externals, get T₁, T₂, T₃ edge-disjoint.
  Together with B, C, D they form a 6-packing, contradicting ν = 4.

  TIER: 1 (finite case analysis on intersection bounds)
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

/-- Triangles sharing edge with e -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

/-- S_e: Externals of e that DON'T share edge with other M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- S_e elements using specific edge {a,b} of e = {a,b,c} -/
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- PAIRWISE INTERSECTION BOUNDS FOR EXTERNAL TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

/-- T₁ = {a,b,w₁} and T₂ = {b,c,w₂} have intersection ⊆ {b} -/
lemma T1_T2_inter_subset (a b c : V) (T₁ T₂ : Finset V) (w₁ w₂ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT2 : T₂ = {b, c, w₂})
    (hc_not_T1 : c ∉ T₁) (ha_not_T2 : a ∉ T₂) :
    T₁ ∩ T₂ ⊆ {b} := by
  intro x hx
  simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
  rw [hT1, hT2] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx.1 with rfl | rfl | rfl
  · -- x = a, but a ∉ T₂
    rw [hT2] at ha_not_T2
    simp only [mem_insert, mem_singleton, not_or] at ha_not_T2
    rcases hx.2 with rfl | rfl | rfl
    · rfl
    · exact absurd rfl ha_not_T2.1
    · exact absurd rfl ha_not_T2.2.1
  · rfl
  · -- x = w₁, show w₁ ∈ T₂ → w₁ = b
    rcases hx.2 with rfl | rfl | rfl
    · rfl
    · rw [hT1] at hc_not_T1
      simp only [mem_insert, mem_singleton, not_or] at hc_not_T1
      exact absurd rfl hc_not_T1.2.2
    · rfl

-- w₁ = w₂ case

lemma T1_T2_inter_card (a b c : V) (T₁ T₂ : Finset V) (w₁ w₂ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT2 : T₂ = {b, c, w₂})
    (hc_not_T1 : c ∉ T₁) (ha_not_T2 : a ∉ T₂) :
    (T₁ ∩ T₂).card ≤ 1 := by
  calc (T₁ ∩ T₂).card ≤ ({b} : Finset V).card := card_le_card (T1_T2_inter_subset a b c T₁ T₂ w₁ w₂ hT1 hT2 hc_not_T1 ha_not_T2)
    _ = 1 := card_singleton b

/-- T₁ = {a,b,w₁} and T₃ = {a,c,w₃} have intersection ⊆ {a} -/
lemma T1_T3_inter_subset (a b c : V) (T₁ T₃ : Finset V) (w₁ w₃ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT3 : T₃ = {a, c, w₃})
    (hc_not_T1 : c ∉ T₁) (hb_not_T3 : b ∉ T₃) :
    T₁ ∩ T₃ ⊆ {a} := by
  intro x hx
  simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
  rw [hT1, hT3] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx.1 with rfl | rfl | rfl
  · rfl
  · -- x = b, but b ∉ T₃
    rw [hT3] at hb_not_T3
    simp only [mem_insert, mem_singleton, not_or] at hb_not_T3
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd rfl hb_not_T3.1.symm
    · exact absurd rfl hb_not_T3.2.1
    · exact absurd rfl hb_not_T3.2.2
  · -- x = w₁
    rcases hx.2 with rfl | rfl | rfl
    · rfl
    · rw [hT1] at hc_not_T1
      simp only [mem_insert, mem_singleton, not_or] at hc_not_T1
      exact absurd rfl hc_not_T1.2.2
    · rfl

-- w₁ = w₃

lemma T1_T3_inter_card (a b c : V) (T₁ T₃ : Finset V) (w₁ w₃ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT3 : T₃ = {a, c, w₃})
    (hc_not_T1 : c ∉ T₁) (hb_not_T3 : b ∉ T₃) :
    (T₁ ∩ T₃).card ≤ 1 := by
  calc (T₁ ∩ T₃).card ≤ ({a} : Finset V).card := card_le_card (T1_T3_inter_subset a b c T₁ T₃ w₁ w₃ hT1 hT3 hc_not_T1 hb_not_T3)
    _ = 1 := card_singleton a

/-- T₂ = {b,c,w₂} and T₃ = {a,c,w₃} have intersection ⊆ {c} -/
lemma T2_T3_inter_subset (a b c : V) (T₂ T₃ : Finset V) (w₂ w₃ : V)
    (hT2 : T₂ = {b, c, w₂}) (hT3 : T₃ = {a, c, w₃})
    (ha_not_T2 : a ∉ T₂) (hb_not_T3 : b ∉ T₃) :
    T₂ ∩ T₃ ⊆ {c} := by
  intro x hx
  simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
  rw [hT2, hT3] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx.1 with rfl | rfl | rfl
  · -- x = b, but b ∉ T₃
    rw [hT3] at hb_not_T3
    simp only [mem_insert, mem_singleton, not_or] at hb_not_T3
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd rfl hb_not_T3.1
    · rfl
    · exact absurd rfl hb_not_T3.2.2
  · rfl
  · -- x = w₂
    rcases hx.2 with rfl | rfl | rfl
    · rw [hT2] at ha_not_T2
      simp only [mem_insert, mem_singleton, not_or] at ha_not_T2
      exact absurd rfl ha_not_T2.2.2
    · rfl
    · rfl

-- w₂ = w₃

lemma T2_T3_inter_card (a b c : V) (T₂ T₃ : Finset V) (w₂ w₃ : V)
    (hT2 : T₂ = {b, c, w₂}) (hT3 : T₃ = {a, c, w₃})
    (ha_not_T2 : a ∉ T₂) (hb_not_T3 : b ∉ T₃) :
    (T₂ ∩ T₃).card ≤ 1 := by
  calc (T₂ ∩ T₃).card ≤ ({c} : Finset V).card := card_le_card (T2_T3_inter_subset a b c T₂ T₃ w₂ w₃ hT2 hT3 ha_not_T2 hb_not_T3)
    _ = 1 := card_singleton c

-- ══════════════════════════════════════════════════════════════════════════════
-- TRIANGLE STRUCTURE EXTRACTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- External triangle in S_e_edge has form {a, b, w} -/
lemma external_has_form (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (a b c : V) (T : Finset V)
    (hT : T ∈ S_e_edge G M a b c) :
    ∃ w, T = {a, b, w} ∧ c ∉ T := by
  simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT
  obtain ⟨⟨hT_tri, _⟩, _, ha, hb, hc⟩ := hT
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
    exact hT_tri.1.card_eq
  -- T has 3 elements including a, b but not c
  -- So T = {a, b, w} for some w ≠ c
  have h_sub : {a, b} ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  -- Find the third element
  have h_card_sub : ({a, b} : Finset V).card ≤ T.card := card_le_card h_sub
  obtain ⟨w, hw_T, hw_ab⟩ : ∃ w ∈ T, w ∉ ({a, b} : Finset V) := by
    by_contra h
    push_neg at h
    have : T ⊆ {a, b} := fun x hx => by
      by_contra hx'
      exact h x hx hx'
    have hcard : T.card ≤ 2 := by
      calc T.card ≤ ({a, b} : Finset V).card := card_le_card this
        _ ≤ 2 := card_insert_le a {b}
    omega
  simp only [mem_insert, mem_singleton, not_or] at hw_ab
  use w
  constructor
  · -- T = {a, b, w}
    ext x
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      by_cases hxa : x = a
      · left; exact hxa
      · by_cases hxb : x = b
        · right; left; exact hxb
        · right; right
          -- x ∈ T, x ≠ a, x ≠ b
          -- Show x = w by card argument
          have h3 : ({a, b, w} : Finset V) ⊆ T := by
            intro y hy
            simp only [mem_insert, mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact ha
            · exact hb
            · exact hw_T
          have hcard_sub : ({a, b, w} : Finset V).card ≤ T.card := card_le_card h3
          have hw_ne_a : w ≠ a := hw_ab.1
          have hw_ne_b : w ≠ b := hw_ab.2
          have hcard3 : ({a, b, w} : Finset V).card = 3 := by
            rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
            · simp [hw_ne_b]
            · simp [hw_ne_a, hw_ne_b]
          have hT_eq : T = {a, b, w} := by
            apply eq_of_subset_of_card_le h3
            omega
          rw [hT_eq] at hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact absurd rfl hxa
          · exact absurd rfl hxb
          · rfl
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hw_T
  · exact hc

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Not all 3 external types can exist
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Assume all 3 types exist (get witnesses T₁, T₂, T₃)
2. By external_has_form: T₁ = {a,b,w₁}, T₂ = {b,c,w₂}, T₃ = {a,c,w₃}
3. S_e definition ensures T_i ∩ f ≤ 1 for other M-elements f
4. Define S = {T₁, T₂, T₃, B, C, D}
5. Show S is a packing (pairwise edge-disjoint)
6. S.card = 6 > 4 = ν(G), contradiction
-/

theorem not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ¬((S_e_edge G M a b c).Nonempty ∧
      (S_e_edge G M b c a).Nonempty ∧
      (S_e_edge G M a c b).Nonempty) := by
  intro ⟨⟨T₁, hT1⟩, ⟨T₂, hT2⟩, ⟨T₃, hT3⟩⟩
  -- Extract triangle structure
  obtain ⟨w₁, hT1_eq, hc_not_T1⟩ := external_has_form G M a b c T₁ hT1
  obtain ⟨w₂, hT2_eq, ha_not_T2⟩ := external_has_form G M b c a T₂ hT2
  obtain ⟨w₃, hT3_eq, hb_not_T3⟩ := external_has_form G M a c b T₃ hT3
  -- Get that T_i are triangles in G
  have hT1_tri : T₁ ∈ G.cliqueFinset 3 := by
    simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT1
    exact hT1.1.1
  have hT2_tri : T₂ ∈ G.cliqueFinset 3 := by
    simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT2
    exact hT2.1.1
  have hT3_tri : T₃ ∈ G.cliqueFinset 3 := by
    simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT3
    exact hT3.1.1
  -- Get S_e properties (edge-disjoint from other M-elements)
  have hT1_Se : T₁ ∈ S_e G M {a, b, c} := by
    simp only [S_e_edge, mem_filter] at hT1
    exact hT1.1
  have hT2_Se : T₂ ∈ S_e G M {b, c, a} := by
    simp only [S_e_edge, mem_filter] at hT2
    have h := hT2.1
    simp only [S_e, trianglesSharingEdge, mem_filter] at h ⊢
    constructor
    · constructor
      · exact h.1.1
      · -- (T₂ ∩ {a,b,c}).card ≥ 2
        have hb : b ∈ T₂ := by
          simp only [S_e_edge, mem_filter] at hT2
          exact hT2.2.1
        have hc : c ∈ T₂ := by
          simp only [S_e_edge, mem_filter] at hT2
          exact hT2.2.2.1
        have h_sub : {b, c} ⊆ T₂ ∩ {a, b, c} := by
          intro x hx
          simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨hb, Or.inr (Or.inl rfl)⟩
          · exact ⟨hc, Or.inr (Or.inr rfl)⟩
        calc (T₂ ∩ {a, b, c}).card ≥ ({b, c} : Finset V).card := card_le_card h_sub
          _ ≥ 2 := by
            rw [card_insert_of_not_mem, card_singleton]
            · omega
            · simp [hbc]
    · exact h.2
  have hT3_Se : T₃ ∈ S_e G M {a, c, b} := by
    simp only [S_e_edge, mem_filter] at hT3
    have h := hT3.1
    simp only [S_e, trianglesSharingEdge, mem_filter] at h ⊢
    constructor
    · constructor
      · exact h.1.1
      · have ha : a ∈ T₃ := by
          simp only [S_e_edge, mem_filter] at hT3
          exact hT3.2.1
        have hc : c ∈ T₃ := by
          simp only [S_e_edge, mem_filter] at hT3
          exact hT3.2.2.1
        have h_sub : {a, c} ⊆ T₃ ∩ {a, b, c} := by
          intro x hx
          simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨ha, Or.inl rfl⟩
          · exact ⟨hc, Or.inr (Or.inr rfl)⟩
        calc (T₃ ∩ {a, b, c}).card ≥ ({a, c} : Finset V).card := card_le_card h_sub
          _ ≥ 2 := by
            rw [card_insert_of_not_mem, card_singleton]
            · omega
            · simp [hac]
    · constructor
      · -- T₃ ≠ {a, b, c}
        intro heq
        rw [heq] at hb_not_T3
        simp only [mem_insert, mem_singleton] at hb_not_T3
        exact hb_not_T3 (Or.inr (Or.inl rfl))
      · intro f hf hf_ne
        -- Need: {a,c,b} = {a,b,c} for the M membership check
        have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        simp only [h_eq] at hf_ne
        exact h.2.2 f hf hf_ne
  -- Extract edge-disjointness from S_e
  simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se hT2_Se hT3_Se
  obtain ⟨_, hT1_ne_E, hT1_disjoint⟩ := hT1_Se
  obtain ⟨_, hT2_ne_E, hT2_disjoint⟩ := hT2_Se
  obtain ⟨_, hT3_ne_E, hT3_disjoint⟩ := hT3_Se
  -- Define the 6-element set
  let S : Finset (Finset V) := {T₁, T₂, T₃, B, C, D}
  -- Prove S is a triangle packing
  have hS_packing : isTrianglePacking G S := by
    constructor
    · -- S ⊆ G.cliqueFinset 3
      intro X hX
      simp only [S, mem_insert, mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · -- Pairwise edge-disjoint
      intro X hX Y hY hXY
      simp only [S, mem_insert, mem_singleton, mem_coe] at hX hY
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hY with rfl | rfl | rfl | rfl | rfl | rfl
      -- 36 cases, but 6 are X = Y (excluded by hXY)
      -- T₁ = T₁ case
      all_goals first | exact absurd rfl hXY | skip
      -- T₁ vs T₂
      · exact T1_T2_inter_card a b c T₁ T₂ w₁ w₂ hT1_eq hT2_eq hc_not_T1 ha_not_T2
      -- T₁ vs T₃
      · exact T1_T3_inter_card a b c T₁ T₃ w₁ w₃ hT1_eq hT3_eq hc_not_T1 hb_not_T3
      -- T₁ vs B
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
        exact hT1_disjoint B hB hB_ne
      -- T₁ vs C
      · exact hT1_disjoint C hC hC_ne
      -- T₁ vs D
      · exact hT1_disjoint D hD hD_ne
      -- T₂ vs T₁
      · rw [inter_comm]; exact T1_T2_inter_card a b c T₁ T₂ w₁ w₂ hT1_eq hT2_eq hc_not_T1 ha_not_T2
      -- T₂ vs T₃
      · exact T2_T3_inter_card a b c T₂ T₃ w₂ w₃ hT2_eq hT3_eq ha_not_T2 hb_not_T3
      -- T₂ vs B
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
        exact hT2_disjoint B hB hB_ne'
      -- T₂ vs C
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {b, c, a} := by rw [h_bca]; exact hC_ne
        exact hT2_disjoint C hC hC_ne'
      -- T₂ vs D
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {b, c, a} := by rw [h_bca]; exact hD_ne
        exact hT2_disjoint D hD hD_ne'
      -- T₃ vs T₁
      · rw [inter_comm]; exact T1_T3_inter_card a b c T₁ T₃ w₁ w₃ hT1_eq hT3_eq hc_not_T1 hb_not_T3
      -- T₃ vs T₂
      · rw [inter_comm]; exact T2_T3_inter_card a b c T₂ T₃ w₂ w₃ hT2_eq hT3_eq ha_not_T2 hb_not_T3
      -- T₃ vs B
      · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {a, c, b} := by rw [h_acb]; exact hB_ne
        exact hT3_disjoint B hB hB_ne'
      -- T₃ vs C
      · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {a, c, b} := by rw [h_acb]; exact hC_ne
        exact hT3_disjoint C hC hC_ne'
      -- T₃ vs D
      · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {a, c, b} := by rw [h_acb]; exact hD_ne
        exact hT3_disjoint D hD hD_ne'
      -- B vs T₁
      · rw [inter_comm]; exact hT1_disjoint B hB hB_ne
      -- B vs T₂
      · rw [inter_comm]
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
        exact hT2_disjoint B hB hB_ne'
      -- B vs T₃
      · rw [inter_comm]
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {a, c, b} := by rw [h_acb]; exact hB_ne
        exact hT3_disjoint B hB hB_ne'
      -- B vs C
      · exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
      -- B vs D
      · exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
      -- C vs T₁
      · rw [inter_comm]; exact hT1_disjoint C hC hC_ne
      -- C vs T₂
      · rw [inter_comm]
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {b, c, a} := by rw [h_bca]; exact hC_ne
        exact hT2_disjoint C hC hC_ne'
      -- C vs T₃
      · rw [inter_comm]
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {a, c, b} := by rw [h_acb]; exact hC_ne
        exact hT3_disjoint C hC hC_ne'
      -- C vs B
      · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
      -- C vs D
      · exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
      -- D vs T₁
      · rw [inter_comm]; exact hT1_disjoint D hD hD_ne
      -- D vs T₂
      · rw [inter_comm]
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {b, c, a} := by rw [h_bca]; exact hD_ne
        exact hT2_disjoint D hD hD_ne'
      -- D vs T₃
      · rw [inter_comm]
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {a, c, b} := by rw [h_acb]; exact hD_ne
        exact hT3_disjoint D hD hD_ne'
      -- D vs B
      · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
      -- D vs C
      · rw [inter_comm]; exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
  -- Show S.card = 6
  have hS_card : S.card = 6 := by
    simp only [S]
    -- Need: T₁, T₂, T₃, B, C, D are all distinct
    have hT1_ne_T2 : T₁ ≠ T₂ := by
      intro heq
      rw [hT1_eq, hT2_eq] at heq
      -- {a, b, w₁} = {b, c, w₂} would require a = c (contradiction) or a = w₂
      have ha_in : a ∈ ({a, b, w₁} : Finset V) := by simp
      rw [heq] at ha_in
      simp only [mem_insert, mem_singleton] at ha_in
      rcases ha_in with rfl | rfl | rfl
      · exact hab (rfl)
      · exact hac rfl
      · exact ha_not_T2 (by rw [hT2_eq]; simp)
    have hT1_ne_T3 : T₁ ≠ T₃ := by
      intro heq
      rw [hT1_eq, hT3_eq] at heq
      have hb_in : b ∈ ({a, b, w₁} : Finset V) := by simp
      rw [heq] at hb_in
      simp only [mem_insert, mem_singleton] at hb_in
      rcases hb_in with rfl | rfl | rfl
      · exact hab rfl
      · exact hbc rfl
      · exact hb_not_T3 (by rw [hT3_eq]; simp)
    have hT2_ne_T3 : T₂ ≠ T₃ := by
      intro heq
      rw [hT2_eq, hT3_eq] at heq
      have hb_in : b ∈ ({b, c, w₂} : Finset V) := by simp
      rw [heq] at hb_in
      simp only [mem_insert, mem_singleton] at hb_in
      rcases hb_in with rfl | rfl | rfl
      · exact hab.symm rfl
      · exact hbc.symm rfl
      · exact hb_not_T3 (by rw [hT3_eq]; simp)
    -- T₁ ∈ S_e means T₁ ≠ E and (T₁ ∩ f).card ≤ 1 for other M-elements
    -- If T₁ = B, then (T₁ ∩ E).card = (B ∩ E).card ≤ 1 (since B ≠ E and M is packing)
    -- But T₁ ∈ S_e means (T₁ ∩ E).card ≥ 2. Contradiction!
    have hT1_ne_B : T₁ ≠ B := by
      intro heq
      have h_inter_ge : (T₁ ∩ {a, b, c}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se
        exact hT1_Se.1.2
      have h_inter_le : (B ∩ {a, b, c}).card ≤ 1 := hM.2 hB (by simp [mem_coe]) hE (by simp [mem_coe]) hB_ne
      rw [heq] at h_inter_ge
      omega
    have hT1_ne_C : T₁ ≠ C := by
      intro heq
      have h_inter_ge : (T₁ ∩ {a, b, c}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se
        exact hT1_Se.1.2
      have h_inter_le : (C ∩ {a, b, c}).card ≤ 1 := hM.2 hC (by simp [mem_coe]) hE (by simp [mem_coe]) hC_ne
      rw [heq] at h_inter_ge
      omega
    have hT1_ne_D : T₁ ≠ D := by
      intro heq
      have h_inter_ge : (T₁ ∩ {a, b, c}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se
        exact hT1_Se.1.2
      have h_inter_le : (D ∩ {a, b, c}).card ≤ 1 := hM.2 hD (by simp [mem_coe]) hE (by simp [mem_coe]) hD_ne
      rw [heq] at h_inter_ge
      omega
    have hT2_ne_B : T₂ ≠ B := by
      intro heq
      have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
      have h_inter_ge : (T₂ ∩ {b, c, a}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT2_Se
        exact hT2_Se.1.2
      rw [h_bca] at h_inter_ge
      have h_inter_le : (B ∩ {a, b, c}).card ≤ 1 := hM.2 hB (by simp [mem_coe]) hE (by simp [mem_coe]) hB_ne
      rw [heq] at h_inter_ge
      omega
    have hT2_ne_C : T₂ ≠ C := by
      intro heq
      have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
      have h_inter_ge : (T₂ ∩ {b, c, a}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT2_Se
        exact hT2_Se.1.2
      rw [h_bca] at h_inter_ge
      have h_inter_le : (C ∩ {a, b, c}).card ≤ 1 := hM.2 hC (by simp [mem_coe]) hE (by simp [mem_coe]) hC_ne
      rw [heq] at h_inter_ge
      omega
    have hT2_ne_D : T₂ ≠ D := by
      intro heq
      have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
      have h_inter_ge : (T₂ ∩ {b, c, a}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT2_Se
        exact hT2_Se.1.2
      rw [h_bca] at h_inter_ge
      have h_inter_le : (D ∩ {a, b, c}).card ≤ 1 := hM.2 hD (by simp [mem_coe]) hE (by simp [mem_coe]) hD_ne
      rw [heq] at h_inter_ge
      omega
    have hT3_ne_B : T₃ ≠ B := by
      intro heq
      have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
      have h_inter_ge : (T₃ ∩ {a, c, b}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT3_Se
        exact hT3_Se.1.2
      rw [h_acb] at h_inter_ge
      have h_inter_le : (B ∩ {a, b, c}).card ≤ 1 := hM.2 hB (by simp [mem_coe]) hE (by simp [mem_coe]) hB_ne
      rw [heq] at h_inter_ge
      omega
    have hT3_ne_C : T₃ ≠ C := by
      intro heq
      have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
      have h_inter_ge : (T₃ ∩ {a, c, b}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT3_Se
        exact hT3_Se.1.2
      rw [h_acb] at h_inter_ge
      have h_inter_le : (C ∩ {a, b, c}).card ≤ 1 := hM.2 hC (by simp [mem_coe]) hE (by simp [mem_coe]) hC_ne
      rw [heq] at h_inter_ge
      omega
    have hT3_ne_D : T₃ ≠ D := by
      intro heq
      have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
      have h_inter_ge : (T₃ ∩ {a, c, b}).card ≥ 2 := by
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT3_Se
        exact hT3_Se.1.2
      rw [h_acb] at h_inter_ge
      have h_inter_le : (D ∩ {a, b, c}).card ≤ 1 := hM.2 hD (by simp [mem_coe]) hE (by simp [mem_coe]) hD_ne
      rw [heq] at h_inter_ge
      omega
    rw [card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem,
        card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
    all_goals simp_all
  -- Apply ν = 4 bound
  have h_bound := hNu4 S hS_packing
  omega

end