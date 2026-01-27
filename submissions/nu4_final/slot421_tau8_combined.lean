/-
  slot421_tau8_combined.lean

  COMBINED PROOF: τ ≤ 8 for PATH_4 with ν = 4

  PROVEN SCAFFOLDING (from slot412):
  - not_all_three_edge_types: ≤2 of 3 edge types have S_e externals (FULL PROOF)
  - All intersection bound lemmas (T1_T2_inter_card, etc.)

  KEY INSIGHT:
  1. For each M-element E, by not_all_three_edge_types, at most 2 edge types have externals
  2. Pick 2 edges covering the non-empty types → covers E and all S_e(E)
  3. For PATH_4 endpoints: selection always includes spine vertex
  4. For PATH_4 middles: ANY 2-edge selection covers both spine vertices (pigeonhole)
  5. Bridges contain spine vertices → covered by adjacent M-element selections
  6. Total: 4 × 2 = 8 edges

  CRITICAL FIX: Cover includes `cover ⊆ G.edgeFinset` constraint (no self-loops)

  TIER: 2 (uses proven not_all_three_edge_types + structural lemmas)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot412)
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

/-- Bridges: triangles sharing edge with e AND with some other M-element -/
def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: PAIRWISE INTERSECTION BOUNDS (from slot412)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: EXTERNAL TRIANGLE STRUCTURE (from slot412)
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
  have h_sub : {a, b} ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: NOT ALL THREE EDGE TYPES (from slot412 - FULL PROOF)
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
      · have hb : b ∈ T₂ := by simp only [S_e_edge, mem_filter] at hT2; exact hT2.2.1
        have hc : c ∈ T₂ := by simp only [S_e_edge, mem_filter] at hT2; exact hT2.2.2.1
        have h_sub : {b, c} ⊆ T₂ ∩ {a, b, c} := by
          intro x hx
          simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨hb, Or.inr (Or.inl rfl)⟩
          · exact ⟨hc, Or.inr (Or.inr rfl)⟩
        calc (T₂ ∩ {a, b, c}).card ≥ ({b, c} : Finset V).card := card_le_card h_sub
          _ ≥ 2 := by rw [card_insert_of_not_mem, card_singleton]; omega; simp [hbc]
    · exact h.2
  have hT3_Se : T₃ ∈ S_e G M {a, c, b} := by
    simp only [S_e_edge, mem_filter] at hT3
    have h := hT3.1
    simp only [S_e, trianglesSharingEdge, mem_filter] at h ⊢
    constructor
    · constructor
      · exact h.1.1
      · have ha : a ∈ T₃ := by simp only [S_e_edge, mem_filter] at hT3; exact hT3.2.1
        have hc : c ∈ T₃ := by simp only [S_e_edge, mem_filter] at hT3; exact hT3.2.2.1
        have h_sub : {a, c} ⊆ T₃ ∩ {a, b, c} := by
          intro x hx
          simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨ha, Or.inl rfl⟩
          · exact ⟨hc, Or.inr (Or.inr rfl)⟩
        calc (T₃ ∩ {a, b, c}).card ≥ ({a, c} : Finset V).card := card_le_card h_sub
          _ ≥ 2 := by rw [card_insert_of_not_mem, card_singleton]; omega; simp [hac]
    · constructor
      · intro heq; rw [heq] at hb_not_T3; simp only [mem_insert, mem_singleton] at hb_not_T3
        exact hb_not_T3 (Or.inr (Or.inl rfl))
      · intro f hf hf_ne
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
      · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
        exact hT1_disjoint B hB hB_ne
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
      · rw [inter_comm]; have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
        exact hT2_disjoint B hB hB_ne'
      · rw [inter_comm]; have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hB_ne' : B ≠ {a, c, b} := by rw [h_acb]; exact hB_ne
        exact hT3_disjoint B hB hB_ne'
      · exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
      · exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
      · rw [inter_comm]; exact hT1_disjoint C hC hC_ne
      · rw [inter_comm]; have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {b, c, a} := by rw [h_bca]; exact hC_ne
        exact hT2_disjoint C hC hC_ne'
      · rw [inter_comm]; have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hC_ne' : C ≠ {a, c, b} := by rw [h_acb]; exact hC_ne
        exact hT3_disjoint C hC hC_ne'
      · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
      · exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
      · rw [inter_comm]; exact hT1_disjoint D hD hD_ne
      · rw [inter_comm]; have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {b, c, a} := by rw [h_bca]; exact hD_ne
        exact hT2_disjoint D hD hD_ne'
      · rw [inter_comm]; have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have hD_ne' : D ≠ {a, c, b} := by rw [h_acb]; exact hD_ne
        exact hT3_disjoint D hD hD_ne'
      · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
      · rw [inter_comm]; exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
  -- Show S.card = 6 and derive contradiction
  have hS_card : S.card = 6 := by
    simp only [S]
    have hT1_ne_T2 : T₁ ≠ T₂ := by
      intro heq; rw [hT1_eq, hT2_eq] at heq
      have ha_in : a ∈ ({a, b, w₁} : Finset V) := by simp
      rw [heq] at ha_in
      simp only [mem_insert, mem_singleton] at ha_in
      rcases ha_in with rfl | rfl | rfl
      · exact hab rfl
      · exact hac rfl
      · exact ha_not_T2 (by rw [hT2_eq]; simp)
    have hT1_ne_T3 : T₁ ≠ T₃ := by
      intro heq; rw [hT1_eq, hT3_eq] at heq
      have hb_in : b ∈ ({a, b, w₁} : Finset V) := by simp
      rw [heq] at hb_in
      simp only [mem_insert, mem_singleton] at hb_in
      rcases hb_in with rfl | rfl | rfl
      · exact hab rfl
      · exact hbc rfl
      · exact hb_not_T3 (by rw [hT3_eq]; simp)
    have hT2_ne_T3 : T₂ ≠ T₃ := by
      intro heq; rw [hT2_eq, hT3_eq] at heq
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
  -- Apply ν = 4 bound
  have h_bound := hNu4 S hS_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge in sym2 if both endpoints in triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- ADAPTIVE EDGE SELECTION (uses not_all_three_edge_types)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
By not_all_three_edge_types, at least one of the 3 edge types has no S_e externals.
Case analysis: pick 2 edges that cover the non-empty types.
- Types 1,2 only: use {a,b}, {b,c} — covers Types 1,2 and element E
- Types 1,3 only: use {a,b}, {a,c} — covers Types 1,3 and element E
- Types 2,3 only: use {b,c}, {a,c} — covers Types 2,3 and element E
All cases: 2 edges from E, both in G.edgeFinset (since E is a clique).
-/

lemma exists_two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hE_clq : {a, b, c} ∈ G.cliqueFinset 3)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      -- Cover the element E = {a,b,c}
      (e₁ ∈ ({a,b,c} : Finset V).sym2 ∨ e₂ ∈ ({a,b,c} : Finset V).sym2) ∧
      -- Cover all S_e externals of E
      (∀ T ∈ S_e G M {a, b, c}, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- By not_all_three_edge_types, at least one type is empty
  have h_not_all := not_all_three_edge_types G M hM hNu4 a b c hE hab hbc hac B C D
    hB hC hD hB_ne hC_ne hD_ne hBC hBD hCD hB_tri hC_tri hD_tri
  push_neg at h_not_all
  -- Get adjacencies from E being a clique
  have hE_clique : G.IsNClique 3 {a, b, c} := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hE_clq
    exact hE_clq.1
  have hab_adj : G.Adj a b := hE_clique.2 (by simp) (by simp) hab
  have hbc_adj : G.Adj b c := hE_clique.2 (by simp) (by simp) hbc
  have hac_adj : G.Adj a c := hE_clique.2 (by simp) (by simp) hac
  -- Case analysis on which type is missing
  by_cases h1 : (S_e_edge G M a b c).Nonempty
  · by_cases h2 : (S_e_edge G M b c a).Nonempty
    · -- Types 1, 2 exist → Type 3 must not exist
      have h3 : ¬(S_e_edge G M a c b).Nonempty := h_not_all h1 h2
      -- Use edges {a,b} and {b,c}
      use s(a, b), s(b, c)
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact SimpleGraph.mem_edgeFinset.mpr hab_adj
      · exact SimpleGraph.mem_edgeFinset.mpr hbc_adj
      · left; exact edge_in_sym2 {a,b,c} a b (by simp) (by simp)
      · intro T hT
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT
        obtain ⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩ := hT
        -- T shares edge with E, so T ∩ E has 2 vertices from {a,b,c}
        -- If {a,b} ⊆ T: edge s(a,b) hits T ✓
        -- If {b,c} ⊆ T: edge s(b,c) hits T ✓
        -- If {a,c} ⊆ T but not a,b or b,c: then T is Type 3 external (c ∉ T not satisfied)
        -- But Type 3 is empty! So this case doesn't occur.
        by_cases hab_in : a ∈ T ∧ b ∈ T
        · left; exact edge_in_sym2 T a b hab_in.1 hab_in.2
        · by_cases hbc_in : b ∈ T ∧ c ∈ T
          · right; exact edge_in_sym2 T b c hbc_in.1 hbc_in.2
          · -- Must have {a,c} ⊆ T
            push_neg at hab_in hbc_in
            have hT_card : T.card = 3 := by
              rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
              exact hT_tri.1.card_eq
            -- T ∩ E has ≥ 2 elements from {a,b,c}
            -- If a ∈ T: either b ∈ T (covered) or c ∈ T
            -- If a ∉ T: then b,c ∈ T (covered by hbc_in contradiction)
            by_cases ha : a ∈ T
            · have hc : c ∈ T := by
                by_contra hc_not
                -- T ∩ E ⊆ {a} since b ∉ T (from hab_in), c ∉ T
                have hb_not : b ∉ T := by
                  intro hb; exact hab_in ⟨ha, hb⟩
                have hsub : T ∩ {a, b, c} ⊆ {a} := by
                  intro x hx
                  simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl
                  · rfl
                  · exact absurd hx.1 hb_not
                  · exact absurd hx.1 hc_not
                have hcard : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                omega
              -- T contains a, c but not b → Type 3 external
              have hb_not : b ∉ T := by intro hb; exact hab_in ⟨ha, hb⟩
              -- T ∈ S_e_edge G M a c b
              have hT_type3 : T ∈ S_e_edge G M a c b := by
                simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter]
                refine ⟨⟨⟨hT_tri, ?_⟩, hT_ne, ?_⟩, ha, hc, hb_not⟩
                · -- (T ∩ {a,c,b}).card ≥ 2
                  have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq]; exact hT_inter
                · -- ∀ f ∈ M, f ≠ {a,c,b} → (T ∩ f).card ≤ 1
                  intro f hf hf_ne
                  have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq] at hf_ne
                  exact hT_disjoint f hf hf_ne
              exact absurd ⟨T, hT_type3⟩ h3
            · -- a ∉ T, so {b,c} ⊆ T (since |T ∩ E| ≥ 2)
              have hb : b ∈ T := by
                by_contra hb_not
                have hc : c ∈ T := by
                  by_contra hc_not
                  have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb_not; exact absurd hx.1 hc_not]
                  have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                  omega
                -- Only c ∈ T from E, contradicts |T ∩ E| ≥ 2
                have hsub : T ∩ {a, b, c} ⊆ {c} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl
                  · exact absurd hx.1 ha
                  · exact absurd hx.1 hb_not
                  · rfl
                have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                omega
              have hc : c ∈ T := by
                by_contra hc_not
                have hsub : T ∩ {a, b, c} ⊆ {b} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl
                  · exact absurd hx.1 ha
                  · rfl
                  · exact absurd hx.1 hc_not
                have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                omega
              exact absurd ⟨hb, hc⟩ hbc_in
    · -- Type 2 doesn't exist, use {a,b} and {a,c}
      use s(a, b), s(a, c)
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact SimpleGraph.mem_edgeFinset.mpr hab_adj
      · exact SimpleGraph.mem_edgeFinset.mpr hac_adj
      · left; exact edge_in_sym2 {a,b,c} a b (by simp) (by simp)
      · intro T hT
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT
        obtain ⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩ := hT
        by_cases hab_in : a ∈ T ∧ b ∈ T
        · left; exact edge_in_sym2 T a b hab_in.1 hab_in.2
        · by_cases hac_in : a ∈ T ∧ c ∈ T
          · right; exact edge_in_sym2 T a c hac_in.1 hac_in.2
          · push_neg at hab_in hac_in
            -- Must have {b,c} ⊆ T → Type 2 external, but Type 2 is empty
            have hT_card : T.card = 3 := by
              rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
              exact hT_tri.1.card_eq
            by_cases ha : a ∈ T
            · -- a ∈ T but neither b nor c (from hab_in, hac_in)
              have hb_not : b ∉ T := by intro hb; exact hab_in ⟨ha, hb⟩
              have hc_not : c ∉ T := by intro hc; exact hac_in ⟨ha, hc⟩
              have hsub : T ∩ {a, b, c} ⊆ {a} := by
                intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl
                · rfl
                · exact absurd hx.1 hb_not
                · exact absurd hx.1 hc_not
              have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
              omega
            · -- a ∉ T, so {b,c} ⊆ T
              have hbc_sub : b ∈ T ∧ c ∈ T := by
                constructor
                · by_contra hb_not
                  by_cases hc : c ∈ T
                  · have hsub : T ∩ {a, b, c} ⊆ {c} := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb_not; rfl]
                    have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                    omega
                  · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb_not; exact absurd hx.1 hc]
                    have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                    omega
                · by_contra hc_not
                  by_cases hb : b ∈ T
                  · have hsub : T ∩ {a, b, c} ⊆ {b} := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; rfl; exact absurd hx.1 hc_not]
                    have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                    omega
                  · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb; exact absurd hx.1 hc_not]
                    have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                    omega
              -- T contains b, c but not a → Type 2 external
              have hT_type2 : T ∈ S_e_edge G M b c a := by
                simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter]
                refine ⟨⟨⟨hT_tri, ?_⟩, hT_ne, ?_⟩, hbc_sub.1, hbc_sub.2, ha⟩
                · have h_eq : ({b, c, a} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq]; exact hT_inter
                · intro f hf hf_ne
                  have h_eq : ({b, c, a} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq] at hf_ne
                  exact hT_disjoint f hf hf_ne
              exact absurd ⟨T, hT_type2⟩ h2
  · -- Type 1 doesn't exist, use {b,c} and {a,c}
    use s(b, c), s(a, c)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact SimpleGraph.mem_edgeFinset.mpr hbc_adj
    · exact SimpleGraph.mem_edgeFinset.mpr hac_adj
    · left; exact edge_in_sym2 {a,b,c} b c (by simp) (by simp)
    · intro T hT
      simp only [S_e, trianglesSharingEdge, mem_filter] at hT
      obtain ⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩ := hT
      by_cases hbc_in : b ∈ T ∧ c ∈ T
      · left; exact edge_in_sym2 T b c hbc_in.1 hbc_in.2
      · by_cases hac_in : a ∈ T ∧ c ∈ T
        · right; exact edge_in_sym2 T a c hac_in.1 hac_in.2
        · push_neg at hbc_in hac_in
          have hT_card : T.card = 3 := by
            rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
            exact hT_tri.1.card_eq
          by_cases hc : c ∈ T
          · have hb_not : b ∉ T := by intro hb; exact hbc_in ⟨hb, hc⟩
            have ha_not : a ∉ T := by intro ha; exact hac_in ⟨ha, hc⟩
            have hsub : T ∩ {a, b, c} ⊆ {c} := by
              intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl
              · exact absurd hx.1 ha_not
              · exact absurd hx.1 hb_not
              · rfl
            have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
            omega
          · -- c ∉ T, so {a,b} ⊆ T
            have hab_sub : a ∈ T ∧ b ∈ T := by
              constructor
              · by_contra ha_not
                by_cases hb : b ∈ T
                · have hsub : T ∩ {a, b, c} ⊆ {b} := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha_not; rfl; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                  omega
                · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha_not; exact absurd hx.1 hb; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                  omega
              · by_contra hb_not
                by_cases ha : a ∈ T
                · have hsub : T ∩ {a, b, c} ⊆ {a} := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                    rcases hx.2 with rfl | rfl | rfl <;> [rfl; exact absurd hx.1 hb_not; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                  omega
                · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb_not; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                  omega
            -- T contains a, b but not c → Type 1 external
            have hT_type1 : T ∈ S_e_edge G M a b c := by
              simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter]
              exact ⟨⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩, hab_sub.1, hab_sub.2, hc⟩
            exact absurd ⟨T, hT_type1⟩ h1

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE LEMMA: Bridge at E-F junction contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_contains_shared (E F : Finset V) (v : V)
    (hEF : E ∩ F = {v})
    (T : Finset V) (hT_card : T.card = 3)
    (hTE : (T ∩ E).card ≥ 2) (hTF : (T ∩ F).card ≥ 2) :
    v ∈ T := by
  by_contra hv_not
  have h_disj : Disjoint (T ∩ E) (T ∩ F) := by
    rw [Finset.disjoint_left]
    intro x hxE hxF
    have hx_inter : x ∈ E ∩ F := mem_inter.mpr ⟨mem_of_mem_inter_right hxE, mem_of_mem_inter_right hxF⟩
    rw [hEF] at hx_inter
    simp only [mem_singleton] at hx_inter
    rw [hx_inter] at hxE
    exact hv_not (mem_of_mem_inter_left hxE)
  have h_union : (T ∩ E ∪ T ∩ F) ⊆ T := union_subset inter_subset_left inter_subset_left
  have h_card : (T ∩ E ∪ T ∩ F).card ≤ T.card := card_le_card h_union
  rw [card_union_of_disjoint h_disj] at h_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- PATH_4 structure: A—v₁—B—v₂—C—v₃—D -/
def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ : V) : Prop :=
  M = {A, B, C, D} ∧
  v₁ ∈ A ∧ v₁ ∈ B ∧ A ∩ B = {v₁} ∧
  v₂ ∈ B ∧ v₂ ∈ C ∧ B ∩ C = {v₂} ∧
  v₃ ∈ C ∧ v₃ ∈ D ∧ C ∩ D = {v₃} ∧
  A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ D = ∅ ∧
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. For each M-element E ∈ {A, B, C, D}:
   - By exists_two_edges_cover_Se, get 2 edges e₁, e₂ ∈ G.edgeFinset
   - These cover E and all S_e(E) externals
2. Total: 4 × 2 = 8 edges
3. Coverage:
   a) M-elements: Each covered by its own 2-edge selection
   b) S_e externals: Covered by the corresponding M-element's selection
   c) Bridges: Share edges with TWO M-elements, contain shared vertex,
      covered by either adjacent M-element's selection
4. Cover ⊆ G.edgeFinset: All edges come from clique adjacencies
-/

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (hPath : isPath4 M A B C D v₁ v₂ v₃)
    (hA_clq : A ∈ G.cliqueFinset 3) (hB_clq : B ∈ G.cliqueFinset 3)
    (hC_clq : C ∈ G.cliqueFinset 3) (hD_clq : D ∈ G.cliqueFinset 3) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  -- Extract PATH_4 structure
  obtain ⟨hM_eq, hv1_A, hv1_B, hAB, hv2_B, hv2_C, hBC, hv3_C, hv3_D, hCD,
          hAC, hAD, hBD, h12, h13, h23⟩ := hPath
  -- Get card 3 for each element
  have hA_card : A.card = 3 := by rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq; exact hA_clq.1.card_eq
  have hB_card : B.card = 3 := by rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq; exact hB_clq.1.card_eq
  have hC_card : C.card = 3 := by rw [SimpleGraph.mem_cliqueFinset_iff] at hC_clq; exact hC_clq.1.card_eq
  have hD_card : D.card = 3 := by rw [SimpleGraph.mem_cliqueFinset_iff] at hD_clq; exact hD_clq.1.card_eq
  -- Get element memberships
  have hA_M : A ∈ M := by rw [hM_eq]; simp
  have hB_M : B ∈ M := by rw [hM_eq]; simp
  have hC_M : C ∈ M := by rw [hM_eq]; simp
  have hD_M : D ∈ M := by rw [hM_eq]; simp
  -- Get distinctness of M-elements
  have hAB_ne : A ≠ B := by
    intro h; rw [h] at hAB; simp at hAB
    have : B.card = 1 := by rw [← hAB]; exact card_singleton v₁
    omega
  have hAC_ne : A ≠ C := by intro h; rw [h] at hAC; simp [inter_self] at hAC
  have hAD_ne : A ≠ D := by intro h; rw [h] at hAD; simp [inter_self] at hAD
  have hBC_ne : B ≠ C := by
    intro h; rw [h] at hBC; simp at hBC
    have : C.card = 1 := by rw [← hBC]; exact card_singleton v₂
    omega
  have hBD_ne : B ≠ D := by intro h; rw [h] at hBD; simp [inter_self] at hBD
  have hCD_ne : C ≠ D := by
    intro h; rw [h] at hCD; simp at hCD
    have : D.card = 1 := by rw [← hCD]; exact card_singleton v₃
    omega
  -- The construction follows from exists_two_edges_cover_Se applied to each M-element
  -- and combining the 8 edges. Bridges are covered by adjacent selections.
  -- This is a Tier 2 proof that Aristotle should complete.
  sorry

end
