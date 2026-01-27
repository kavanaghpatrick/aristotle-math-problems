/-
  slot413_tau_le_8_unified.lean

  UNIFIED PROOF: tau <= 8 for PATH_4 with nu = 4

  STRATEGY:
  This combines:
  1. slot412's not_all_three_edge_types (for S_e externals)
  2. Bridge analysis (triangles sharing edges with 2+ M-elements)

  KEY INSIGHT: Triangles partition into:
  - M-elements (4 triangles, covered by any edge)
  - S_e externals (share edge with exactly 1 M-element)
  - Bridges (share edges with 2+ M-elements)

  For S_e externals: slot412 shows 2 edges per M-element suffice
  For bridges: They must use spine vertices, covered by B/C edges

  TIER: 2 (uses proven scaffolding from slot412)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ==============================================================================
-- DEFINITIONS (from slot412)
-- ==============================================================================

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

-- ==============================================================================
-- BRIDGE DEFINITION
-- ==============================================================================

/-- Bridge: triangle sharing edges with 2+ distinct M-elements -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ∉ M ∧
  ∃ E₁ E₂ : Finset V, E₁ ∈ M ∧ E₂ ∈ M ∧ E₁ ≠ E₂ ∧
    (T ∩ E₁).card ≥ 2 ∧ (T ∩ E₂).card ≥ 2

/-- Set of bridges -/
def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => T ∉ M ∧
    ∃ E₁ ∈ M, ∃ E₂ ∈ M, E₁ ≠ E₂ ∧ (T ∩ E₁).card ≥ 2 ∧ (T ∩ E₂).card ≥ 2)

-- ==============================================================================
-- PATH_4 DEFINITION
-- ==============================================================================

def isPath4Labeled (M : Finset (Finset V)) (A B C D : Finset V)
    (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V) : Prop :=
  M = {A, B, C, D} ∧
  A = {v₁, a₂, a₃} ∧ B = {v₁, v₂, b₃} ∧ C = {v₂, v₃, c₃} ∧ D = {v₃, d₂, d₃} ∧
  -- All 9 vertices distinct
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ v₁ ≠ b₃ ∧ v₁ ≠ c₃ ∧ v₁ ≠ d₂ ∧ v₁ ≠ d₃ ∧
  v₂ ≠ v₃ ∧ v₂ ≠ a₂ ∧ v₂ ≠ a₃ ∧ v₂ ≠ b₃ ∧ v₂ ≠ c₃ ∧ v₂ ≠ d₂ ∧ v₂ ≠ d₃ ∧
  v₃ ≠ a₂ ∧ v₃ ≠ a₃ ∧ v₃ ≠ b₃ ∧ v₃ ≠ c₃ ∧ v₃ ≠ d₂ ∧ v₃ ≠ d₃ ∧
  a₂ ≠ a₃ ∧ a₂ ≠ b₃ ∧ a₂ ≠ c₃ ∧ a₂ ≠ d₂ ∧ a₂ ≠ d₃ ∧
  a₃ ≠ b₃ ∧ a₃ ≠ c₃ ∧ a₃ ≠ d₂ ∧ a₃ ≠ d₃ ∧
  b₃ ≠ c₃ ∧ b₃ ≠ d₂ ∧ b₃ ≠ d₃ ∧
  c₃ ≠ d₂ ∧ c₃ ≠ d₃ ∧
  d₂ ≠ d₃

-- ==============================================================================
-- PROVEN SCAFFOLDING FROM slot412
-- ==============================================================================

/-- T₁ = {a,b,w₁} and T₂ = {b,c,w₂} have intersection subset {b} -/
lemma T1_T2_inter_subset (a b c : V) (T₁ T₂ : Finset V) (w₁ w₂ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT2 : T₂ = {b, c, w₂})
    (hc_not_T1 : c ∉ T₁) (ha_not_T2 : a ∉ T₂) :
    T₁ ∩ T₂ ⊆ {b} := by
  intro x hx
  simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
  rw [hT1, hT2] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx.1 with rfl | rfl | rfl
  · rw [hT2] at ha_not_T2
    simp only [mem_insert, mem_singleton, not_or] at ha_not_T2
    rcases hx.2 with rfl | rfl | rfl
    · rfl
    · exact absurd rfl ha_not_T2.1
    · exact absurd rfl ha_not_T2.2.1
  · rfl
  · rcases hx.2 with rfl | rfl | rfl
    · rfl
    · rw [hT1] at hc_not_T1
      simp only [mem_insert, mem_singleton, not_or] at hc_not_T1
      exact absurd rfl hc_not_T1.2.2
    · rfl

lemma T1_T2_inter_card (a b c : V) (T₁ T₂ : Finset V) (w₁ w₂ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT2 : T₂ = {b, c, w₂})
    (hc_not_T1 : c ∉ T₁) (ha_not_T2 : a ∉ T₂) :
    (T₁ ∩ T₂).card ≤ 1 := by
  calc (T₁ ∩ T₂).card ≤ ({b} : Finset V).card := card_le_card (T1_T2_inter_subset a b c T₁ T₂ w₁ w₂ hT1 hT2 hc_not_T1 ha_not_T2)
    _ = 1 := card_singleton b

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
  · rw [hT3] at hb_not_T3
    simp only [mem_insert, mem_singleton, not_or] at hb_not_T3
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd rfl hb_not_T3.1.symm
    · exact absurd rfl hb_not_T3.2.1
    · exact absurd rfl hb_not_T3.2.2
  · rcases hx.2 with rfl | rfl | rfl
    · rfl
    · rw [hT1] at hc_not_T1
      simp only [mem_insert, mem_singleton, not_or] at hc_not_T1
      exact absurd rfl hc_not_T1.2.2
    · rfl

lemma T1_T3_inter_card (a b c : V) (T₁ T₃ : Finset V) (w₁ w₃ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT3 : T₃ = {a, c, w₃})
    (hc_not_T1 : c ∉ T₁) (hb_not_T3 : b ∉ T₃) :
    (T₁ ∩ T₃).card ≤ 1 := by
  calc (T₁ ∩ T₃).card ≤ ({a} : Finset V).card := card_le_card (T1_T3_inter_subset a b c T₁ T₃ w₁ w₃ hT1 hT3 hc_not_T1 hb_not_T3)
    _ = 1 := card_singleton a

lemma T2_T3_inter_subset (a b c : V) (T₂ T₃ : Finset V) (w₂ w₃ : V)
    (hT2 : T₂ = {b, c, w₂}) (hT3 : T₃ = {a, c, w₃})
    (ha_not_T2 : a ∉ T₂) (hb_not_T3 : b ∉ T₃) :
    T₂ ∩ T₃ ⊆ {c} := by
  intro x hx
  simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
  rw [hT2, hT3] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx.1 with rfl | rfl | rfl
  · rw [hT3] at hb_not_T3
    simp only [mem_insert, mem_singleton, not_or] at hb_not_T3
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd rfl hb_not_T3.1
    · rfl
    · exact absurd rfl hb_not_T3.2.2
  · rfl
  · rcases hx.2 with rfl | rfl | rfl
    · rw [hT2] at ha_not_T2
      simp only [mem_insert, mem_singleton, not_or] at ha_not_T2
      exact absurd rfl ha_not_T2.2.2
    · rfl
    · rfl

lemma T2_T3_inter_card (a b c : V) (T₂ T₃ : Finset V) (w₂ w₃ : V)
    (hT2 : T₂ = {b, c, w₂}) (hT3 : T₃ = {a, c, w₃})
    (ha_not_T2 : a ∉ T₂) (hb_not_T3 : b ∉ T₃) :
    (T₂ ∩ T₃).card ≤ 1 := by
  calc (T₂ ∩ T₃).card ≤ ({c} : Finset V).card := card_le_card (T2_T3_inter_subset a b c T₂ T₃ w₂ w₃ hT2 hT3 ha_not_T2 hb_not_T3)
    _ = 1 := card_singleton c

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
  have h_sub : {a, b} ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
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
  · ext x
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      by_cases hxa : x = a
      · left; exact hxa
      · by_cases hxb : x = b
        · right; left; exact hxb
        · right; right
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

-- ==============================================================================
-- KEY THEOREM: Not all 3 S_e edge types can coexist (from slot412)
-- ==============================================================================

/-
PROOF SKETCH:
1. Assume all 3 types exist (get witnesses T₁, T₂, T₃)
2. By external_has_form: T₁ = {a,b,w₁}, T₂ = {b,c,w₂}, T₃ = {a,c,w₃}
3. S_e definition ensures T_i ∩ f <= 1 for other M-elements f
4. Define S = {T₁, T₂, T₃, B, C, D}
5. Show S is a packing (pairwise edge-disjoint)
6. S.card = 6 > 4 = nu(G), contradiction
-/
theorem not_all_three_S_e_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
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
  obtain ⟨w₁, hT1_eq, hc_not_T1⟩ := external_has_form G M a b c T₁ hT1
  obtain ⟨w₂, hT2_eq, ha_not_T2⟩ := external_has_form G M b c a T₂ hT2
  obtain ⟨w₃, hT3_eq, hb_not_T3⟩ := external_has_form G M a c b T₃ hT3
  have hT1_tri : T₁ ∈ G.cliqueFinset 3 := by
    simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT1
    exact hT1.1.1
  have hT2_tri : T₂ ∈ G.cliqueFinset 3 := by
    simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT2
    exact hT2.1.1
  have hT3_tri : T₃ ∈ G.cliqueFinset 3 := by
    simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT3
    exact hT3.1.1
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
      · have hb : b ∈ T₂ := by
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
      · intro heq
        rw [heq] at hb_not_T3
        simp only [mem_insert, mem_singleton] at hb_not_T3
        exact hb_not_T3 (Or.inr (Or.inl rfl))
      · intro f hf hf_ne
        have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        simp only [h_eq] at hf_ne
        exact h.2.2 f hf hf_ne
  simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se hT2_Se hT3_Se
  obtain ⟨_, hT1_ne_E, hT1_disjoint⟩ := hT1_Se
  obtain ⟨_, hT2_ne_E, hT2_disjoint⟩ := hT2_Se
  obtain ⟨_, hT3_ne_E, hT3_disjoint⟩ := hT3_Se
  let S : Finset (Finset V) := {T₁, T₂, T₃, B, C, D}
  have hS_packing : isTrianglePacking G S := by
    constructor
    · intro X hX
      simp only [S, mem_insert, mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · intro X hX Y hY hXY
      simp only [S, mem_insert, mem_singleton, mem_coe] at hX hY
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hY with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl hXY | skip
      · exact T1_T2_inter_card a b c T₁ T₂ w₁ w₂ hT1_eq hT2_eq hc_not_T1 ha_not_T2
      · exact T1_T3_inter_card a b c T₁ T₃ w₁ w₃ hT1_eq hT3_eq hc_not_T1 hb_not_T3
      · exact hT1_disjoint B hB hB_ne
      · exact hT1_disjoint C hC hC_ne
      · exact hT1_disjoint D hD hD_ne
      · rw [inter_comm]; exact T1_T2_inter_card a b c T₁ T₂ w₁ w₂ hT1_eq hT2_eq hc_not_T1 ha_not_T2
      · exact T2_T3_inter_card a b c T₂ T₃ w₂ w₃ hT2_eq hT3_eq ha_not_T2 hb_not_T3
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
        exact hT2_disjoint B hB hB_ne'
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {b, c, a} := by rw [h_bca]; exact hC_ne
        exact hT2_disjoint C hC hC_ne'
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {b, c, a} := by rw [h_bca]; exact hD_ne
        exact hT2_disjoint D hD hD_ne'
      · rw [inter_comm]; exact T1_T3_inter_card a b c T₁ T₃ w₁ w₃ hT1_eq hT3_eq hc_not_T1 hb_not_T3
      · rw [inter_comm]; exact T2_T3_inter_card a b c T₂ T₃ w₂ w₃ hT2_eq hT3_eq ha_not_T2 hb_not_T3
      · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {a, c, b} := by rw [h_acb]; exact hB_ne
        exact hT3_disjoint B hB hB_ne'
      · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {a, c, b} := by rw [h_acb]; exact hC_ne
        exact hT3_disjoint C hC hC_ne'
      · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {a, c, b} := by rw [h_acb]; exact hD_ne
        exact hT3_disjoint D hD hD_ne'
      · rw [inter_comm]; exact hT1_disjoint B hB hB_ne
      · rw [inter_comm]
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
        exact hT2_disjoint B hB hB_ne'
      · rw [inter_comm]
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {a, c, b} := by rw [h_acb]; exact hB_ne
        exact hT3_disjoint B hB hB_ne'
      · exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
      · exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
      · rw [inter_comm]; exact hT1_disjoint C hC hC_ne
      · rw [inter_comm]
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {b, c, a} := by rw [h_bca]; exact hC_ne
        exact hT2_disjoint C hC hC_ne'
      · rw [inter_comm]
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {a, c, b} := by rw [h_acb]; exact hC_ne
        exact hT3_disjoint C hC hC_ne'
      · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
      · exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
      · rw [inter_comm]; exact hT1_disjoint D hD hD_ne
      · rw [inter_comm]
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {b, c, a} := by rw [h_bca]; exact hD_ne
        exact hT2_disjoint D hD hD_ne'
      · rw [inter_comm]
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {a, c, b} := by rw [h_acb]; exact hD_ne
        exact hT3_disjoint D hD hD_ne'
      · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
      · rw [inter_comm]; exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
  have hS_card : S.card = 6 := by
    simp only [S]
    have hT1_ne_T2 : T₁ ≠ T₂ := by
      intro heq
      rw [hT1_eq, hT2_eq] at heq
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
  have h_bound := hNu4 S hS_packing
  omega

-- ==============================================================================
-- TRIANGLE CLASSIFICATION
-- ==============================================================================

/-- Every non-M triangle shares an edge with at least one M-element -/
lemma non_M_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_not_M : T ∉ M) :
    ∃ E ∈ M, (T ∩ E).card ≥ 2 := hMaximal T hT hT_not_M

/-- Triangle is an S_e-external of E if it shares edge with E but not with other M-elements -/
def isSExternal (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (E T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ≠ E ∧ (T ∩ E).card ≥ 2 ∧
  ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1

-- ==============================================================================
-- ADAPTIVE COVER CONSTRUCTION
-- ==============================================================================

/-
PROOF SKETCH for exists_two_S_e_edges:
By not_all_three_S_e_edge_types, at least one S_e edge type is empty.
Case analysis on which type is missing determines which 2 edges cover all S_e externals.
These 2 edges also cover E itself (any edge of E covers E).
-/
lemma exists_two_S_e_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ (e₁ e₂ : Sym2 V),
      -- Both edges are in G
      e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      -- Both edges are edges of E (cover E)
      e₁ ∈ ({a,b,c} : Finset V).sym2 ∧ e₂ ∈ ({a,b,c} : Finset V).sym2 ∧
      -- Together they cover all S_e externals of E
      ∀ T ∈ S_e G M {a, b, c}, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  -- By not_all_three_S_e_edge_types, at least one type is empty
  have h_not_all := not_all_three_S_e_edge_types G M hM hNu4 a b c hE hab hbc hac
    B C D hB hC hD hB_ne hC_ne hD_ne hBC hBD hCD hB_tri hC_tri hD_tri
  push_neg at h_not_all
  -- Get edges in G from E being a clique
  have hE_clique := hM.1 hE
  rw [SimpleGraph.mem_cliqueFinset_iff] at hE_clique
  have hab_adj : G.Adj a b := hE_clique.1 (by simp) (by simp) hab
  have hbc_adj : G.Adj b c := hE_clique.1 (by simp) (by simp) hbc
  have hac_adj : G.Adj a c := hE_clique.1 (by simp) (by simp) hac
  -- Case analysis
  by_cases h1 : (S_e_edge G M a b c).Nonempty
  · by_cases h2 : (S_e_edge G M b c a).Nonempty
    · -- Types 1, 2 exist → Type 3 must not exist
      have h3 : ¬(S_e_edge G M a c b).Nonempty := h_not_all h1 h2
      -- Use edges {a,b} and {b,c}
      use s(a, b), s(b, c)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset]; exact hab_adj
      · rw [SimpleGraph.mem_edgeFinset]; exact hbc_adj
      · simp [Sym2.mem_iff]
      · simp [Sym2.mem_iff]
      · intro T hT
        -- T ∈ S_e, so T uses one of the 3 edges
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT
        obtain ⟨⟨hT_tri, hT_share⟩, hT_ne, hT_disjoint⟩ := hT
        -- T shares edge with E = {a,b,c}, so T contains 2 of {a,b,c}
        -- Case split: which 2 vertices does T contain?
        by_cases ha_T : a ∈ T
        · by_cases hb_T : b ∈ T
          · -- T contains {a,b} → covered by s(a,b)
            left
            simp only [Finset.mem_sym2_iff]
            use a, b
            exact ⟨ha_T, hb_T, rfl⟩
          · -- T contains a but not b, must contain c
            by_cases hc_T : c ∈ T
            · -- T contains {a,c} → Type 3 external
              -- But Type 3 is empty, contradiction
              exfalso
              apply h3
              use T
              simp only [S_e_edge, mem_filter]
              refine ⟨?_, ha_T, hc_T, hb_T⟩
              simp only [S_e, trianglesSharingEdge, mem_filter]
              constructor
              · exact ⟨hT_tri, hT_share⟩
              · exact ⟨hT_ne, hT_disjoint⟩
            · -- T contains only a from {a,b,c}, but intersection >= 2
              exfalso
              have h_sub : T ∩ {a, b, c} ⊆ {a} := by
                intro x hx
                simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl
                · rfl
                · exact absurd hx.1 hb_T
                · exact absurd hx.1 hc_T
              have hcard : (T ∩ {a, b, c}).card ≤ 1 := by
                calc (T ∩ {a, b, c}).card ≤ ({a} : Finset V).card := card_le_card h_sub
                  _ = 1 := card_singleton a
              omega
        · -- T doesn't contain a
          by_cases hb_T : b ∈ T
          · by_cases hc_T : c ∈ T
            · -- T contains {b,c} → covered by s(b,c)
              right
              simp only [Finset.mem_sym2_iff]
              use b, c
              exact ⟨hb_T, hc_T, rfl⟩
            · -- T contains only b from {a,b,c}
              exfalso
              have h_sub : T ∩ {a, b, c} ⊆ {b} := by
                intro x hx
                simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl
                · exact absurd hx.1 ha_T
                · rfl
                · exact absurd hx.1 hc_T
              have hcard : (T ∩ {a, b, c}).card ≤ 1 := by
                calc (T ∩ {a, b, c}).card ≤ ({b} : Finset V).card := card_le_card h_sub
                  _ = 1 := card_singleton b
              omega
          · -- T doesn't contain a or b, intersection < 2
            exfalso
            have h_sub : T ∩ {a, b, c} ⊆ {c} := by
              intro x hx
              simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl
              · exact absurd hx.1 ha_T
              · exact absurd hx.1 hb_T
              · rfl
            have hcard : (T ∩ {a, b, c}).card ≤ 1 := by
              calc (T ∩ {a, b, c}).card ≤ ({c} : Finset V).card := card_le_card h_sub
                _ = 1 := card_singleton c
            omega
    · -- Type 2 doesn't exist, use {a,b} and {a,c}
      use s(a, b), s(a, c)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset]; exact hab_adj
      · rw [SimpleGraph.mem_edgeFinset]; exact hac_adj
      · simp [Sym2.mem_iff]
      · simp [Sym2.mem_iff]
      · intro T hT
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT
        obtain ⟨⟨hT_tri, hT_share⟩, hT_ne, hT_disjoint⟩ := hT
        by_cases ha_T : a ∈ T
        · by_cases hb_T : b ∈ T
          · left; simp only [Finset.mem_sym2_iff]; use a, b; exact ⟨ha_T, hb_T, rfl⟩
          · by_cases hc_T : c ∈ T
            · right; simp only [Finset.mem_sym2_iff]; use a, c; exact ⟨ha_T, hc_T, rfl⟩
            · exfalso
              have h_sub : T ∩ {a, b, c} ⊆ {a} := by
                intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl <;> [rfl; exact absurd hx.1 hb_T; exact absurd hx.1 hc_T]
              have : (T ∩ {a, b, c}).card ≤ 1 := by calc (T ∩ {a,b,c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton a).le
              omega
        · by_cases hb_T : b ∈ T
          · by_cases hc_T : c ∈ T
            · -- Type 2: {b,c,w}, but Type 2 is empty
              exfalso; apply h2; use T
              simp only [S_e_edge, mem_filter]
              refine ⟨?_, hb_T, hc_T, ha_T⟩
              simp only [S_e, trianglesSharingEdge, mem_filter]
              exact ⟨⟨hT_tri, hT_share⟩, hT_ne, hT_disjoint⟩
            · exfalso
              have h_sub : T ∩ {a, b, c} ⊆ {b} := by
                intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha_T; rfl; exact absurd hx.1 hc_T]
              have : (T ∩ {a, b, c}).card ≤ 1 := by calc (T ∩ {a,b,c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton b).le
              omega
          · exfalso
            have h_sub : T ∩ {a, b, c} ⊆ {c} := by
              intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha_T; exact absurd hx.1 hb_T; rfl]
            have : (T ∩ {a, b, c}).card ≤ 1 := by calc (T ∩ {a,b,c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton c).le
            omega
  · -- Type 1 doesn't exist, use {b,c} and {a,c}
    use s(b, c), s(a, c)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset]; exact hbc_adj
    · rw [SimpleGraph.mem_edgeFinset]; exact hac_adj
    · simp [Sym2.mem_iff]
    · simp [Sym2.mem_iff]
    · intro T hT
      simp only [S_e, trianglesSharingEdge, mem_filter] at hT
      obtain ⟨⟨hT_tri, hT_share⟩, hT_ne, hT_disjoint⟩ := hT
      by_cases ha_T : a ∈ T
      · by_cases hb_T : b ∈ T
        · -- Type 1: {a,b,w}, but Type 1 is empty
          exfalso; apply h1; use T
          simp only [S_e_edge, mem_filter]
          by_cases hc_T : c ∈ T
          · -- T = {a,b,c} = E, but T ≠ E
            exfalso
            have hT_card : T.card = 3 := by
              rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
              exact hT_tri.1.card_eq
            have h_sub : {a, b, c} ⊆ T := by
              intro x hx; simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            have : T = {a, b, c} := by
              apply eq_of_subset_of_card_le h_sub
              rw [hT_card, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
              · simp [hbc]
              · simp [hab, hac]
            exact hT_ne this
          · refine ⟨?_, ha_T, hb_T, hc_T⟩
            simp only [S_e, trianglesSharingEdge, mem_filter]
            exact ⟨⟨hT_tri, hT_share⟩, hT_ne, hT_disjoint⟩
        · by_cases hc_T : c ∈ T
          · right; simp only [Finset.mem_sym2_iff]; use a, c; exact ⟨ha_T, hc_T, rfl⟩
          · exfalso
            have h_sub : T ∩ {a, b, c} ⊆ {a} := by
              intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl <;> [rfl; exact absurd hx.1 hb_T; exact absurd hx.1 hc_T]
            have : (T ∩ {a, b, c}).card ≤ 1 := by calc (T ∩ {a,b,c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton a).le
            omega
      · by_cases hb_T : b ∈ T
        · by_cases hc_T : c ∈ T
          · left; simp only [Finset.mem_sym2_iff]; use b, c; exact ⟨hb_T, hc_T, rfl⟩
          · exfalso
            have h_sub : T ∩ {a, b, c} ⊆ {b} := by
              intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha_T; rfl; exact absurd hx.1 hc_T]
            have : (T ∩ {a, b, c}).card ≤ 1 := by calc (T ∩ {a,b,c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton b).le
            omega
        · exfalso
          have h_sub : T ∩ {a, b, c} ⊆ {c} := by
            intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
            rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha_T; exact absurd hx.1 hb_T; rfl]
          have : (T ∩ {a, b, c}).card ≤ 1 := by calc (T ∩ {a,b,c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton c).le
          omega

-- ==============================================================================
-- BRIDGE HANDLING FOR PATH_4
-- ==============================================================================

/-
PROOF SKETCH:
In PATH_4, bridges (triangles sharing edges with 2+ M-elements) must use spine vertices.
The spine edges {v1,v2} (in B) and {v2,v3} (in C) are covered by the edges chosen for B and C.

Key observation: A bridge T sharing edge with both E and F must contain:
- 2 vertices from E
- 2 vertices from F
- Since |T| = 3, this means |E ∩ F| >= 1 (shared vertex on spine)

For PATH_4 with A-B-C-D:
- Only consecutive pairs share vertices (A-B share v1, B-C share v2, C-D share v3)
- So bridges only exist between consecutive M-elements
- A bridge between B and C contains {v2} and two other vertices
- The edge {v2, ?} from either B or C's cover hits this bridge
-/

/-- In PATH_4, bridges must use spine vertices -/
lemma bridge_uses_spine_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (T : Finset V) (hT_bridge : isBridge G M T) :
    v₁ ∈ T ∨ v₂ ∈ T ∨ v₃ ∈ T := by
  obtain ⟨hT_tri, hT_not_M, E₁, E₂, hE1, hE2, hE_ne, h1, h2⟩ := hT_bridge
  -- T shares edge with E₁ and E₂
  -- In PATH_4, E₁ and E₂ are among {A, B, C, D}
  -- Only consecutive pairs share vertices
  -- If E₁ and E₂ are non-consecutive, their intersection is empty
  -- But T shares edge (2 vertices) with each, so if E₁ ∩ E₂ = ∅, then |T| >= 4, contradiction
  sorry

-- ==============================================================================
-- MAIN THEOREM: tau <= 8 for PATH_4
-- ==============================================================================

/-
PROOF SKETCH:
1. For each M-element E, choose 2 edges adaptively (by exists_two_S_e_edges)
2. These 8 edges cover:
   - All M-elements (each E is covered by one of its own chosen edges)
   - All S_e externals (by construction of exists_two_S_e_edges)
   - All bridges (must use spine, covered by edges from consecutive elements)
3. By maximality, every triangle shares edge with some M-element, so is covered
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  sorry

end
