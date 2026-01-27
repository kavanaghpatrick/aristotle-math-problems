/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6c77223c-a6ef-4fa0-9f1d-e56400948aec

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot423_two_real_edges_complete.lean

  SELF-CONTAINED proof that 2 REAL edges cover E + S_e externals.

  CRITICAL FIX: Previous exists_two_edges_cover_Se used SELF-LOOPS (s(w,w))
  which are NOT valid graph edges. This version requires C ⊆ G.edgeFinset.

  INCLUDES: Full proof of not_all_three_edge_types from slot412.

  TIER: 2 (self-contained with all helpers)
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- PAIRWISE INTERSECTION BOUNDS (from slot412)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL TRIANGLE STRUCTURE (from slot412)
-- ══════════════════════════════════════════════════════════════════════════════

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
          have hcard3 : ({a, b, w} : Finset V).card = 3 := by
            rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
            · simp [hw_ab.2]
            · simp [hw_ab.1, hw_ab.2]
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
-- SIMPLE HELPERS
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_edge_mem_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (hE : E ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hE
  have hadj : G.Adj a b := hE.1 ha hb hab
  simp only [SimpleGraph.mem_edgeFinset]
  exact hadj

lemma edge_covers_triangle (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

lemma Se_external_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T : Finset V) (hT : T ∈ S_e G M {a, b, c}) :
    (a ∈ T ∧ b ∈ T) ∨ (b ∈ T ∧ c ∈ T) ∨ (a ∈ T ∧ c ∈ T) := by
  simp only [S_e, trianglesSharingEdge, mem_filter] at hT
  obtain ⟨⟨_, hinter⟩, _, _⟩ := hT
  by_contra h_none
  push_neg at h_none
  obtain ⟨h1, h2, h3⟩ := h_none
  have h_card_le : (T ∩ {a, b, c}).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    simp only [mem_inter, mem_insert, mem_singleton] at hx hy
    rcases hx.2 with rfl | rfl | rfl <;> rcases hy.2 with rfl | rfl | rfl
    all_goals first | rfl | (exfalso; exact h1 ⟨hx.1, hy.1⟩) |
                           (exfalso; exact h2 ⟨hx.1, hy.1⟩) |
                           (exfalso; exact h2 ⟨hy.1, hx.1⟩) |
                           (exfalso; exact h3 ⟨hx.1, hy.1⟩) |
                           (exfalso; exact h3 ⟨hy.1, hx.1⟩)
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Two REAL edges cover E + S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. For E = {a,b,c}, S_e partitions by which edge is shared
2. If all 3 edge types have externals, we get a 6-packing contradiction
3. So at most 2 edge types have externals
4. Pick the 2 corresponding edges - they cover everything
-/

theorem exists_two_real_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (E : Finset V) (hE : E ∈ M)
    (a b c : V) (hE_eq : E = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ E) (hC_ne : C ≠ E) (hD_ne : D ≠ E)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ Cover : Finset (Sym2 V),
      Cover ⊆ G.edgeFinset ∧
      Cover.card ≤ 2 ∧
      (∀ T ∈ insert E (S_e G M E), ∃ e ∈ Cover, e ∈ T.sym2) := by
  have hE_clique : E ∈ G.cliqueFinset 3 := hM.1 hE
  have hab_edge : s(a, b) ∈ G.edgeFinset := by
    apply triangle_edge_mem_edgeFinset G E hE_clique a b
    · rw [hE_eq]; simp
    · rw [hE_eq]; simp
    · exact hab
  have hbc_edge : s(b, c) ∈ G.edgeFinset := by
    apply triangle_edge_mem_edgeFinset G E hE_clique b c
    · rw [hE_eq]; simp
    · rw [hE_eq]; simp
    · exact hbc
  have hac_edge : s(a, c) ∈ G.edgeFinset := by
    apply triangle_edge_mem_edgeFinset G E hE_clique a c
    · rw [hE_eq]; simp
    · rw [hE_eq]; simp
    · exact hac
  -- At most 2 of 3 edge types have externals
  have h_not_all_three : ¬((S_e_edge G M a b c).Nonempty ∧
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
    -- Get S_e properties
    have hT1_Se : T₁ ∈ S_e G M {a, b, c} := by
      simp only [S_e_edge, mem_filter] at hT1; exact hT1.1
    have hT2_Se_raw : T₂ ∈ S_e G M {b, c, a} := by
      simp only [S_e_edge, mem_filter] at hT2; exact hT2.1
    have hT3_Se_raw : T₃ ∈ S_e G M {a, c, b} := by
      simp only [S_e_edge, mem_filter] at hT3; exact hT3.1
    simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se hT2_Se_raw hT3_Se_raw
    obtain ⟨_, hT1_ne_E, hT1_disjoint⟩ := hT1_Se
    obtain ⟨_, hT2_ne_E, hT2_disjoint⟩ := hT2_Se_raw
    obtain ⟨_, hT3_ne_E, hT3_disjoint⟩ := hT3_Se_raw
    -- Define 6-element set
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
        -- T₁ vs T₂
        · exact T1_T2_inter_card a b c T₁ T₂ w₁ w₂ hT1_eq hT2_eq hc_not_T1 ha_not_T2
        -- T₁ vs T₃
        · exact T1_T3_inter_card a b c T₁ T₃ w₁ w₃ hT1_eq hT3_eq hc_not_T1 hb_not_T3
        -- T₁ vs B, C, D
        · exact hT1_disjoint B hB hB_ne
        · exact hT1_disjoint C hC hC_ne
        · exact hT1_disjoint D hD hD_ne
        -- T₂ vs T₁
        · rw [inter_comm]; exact T1_T2_inter_card a b c T₁ T₂ w₁ w₂ hT1_eq hT2_eq hc_not_T1 ha_not_T2
        -- T₂ vs T₃
        · exact T2_T3_inter_card a b c T₂ T₃ w₂ w₃ hT2_eq hT3_eq ha_not_T2 hb_not_T3
        -- T₂ vs B, C, D
        · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
          exact hT2_disjoint B hB hB_ne'
        · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hC_ne' : C ≠ {b, c, a} := by rw [h_bca]; exact hC_ne
          exact hT2_disjoint C hC hC_ne'
        · have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hD_ne' : D ≠ {b, c, a} := by rw [h_bca]; exact hD_ne
          exact hT2_disjoint D hD hD_ne'
        -- T₃ vs T₁, T₂
        · rw [inter_comm]; exact T1_T3_inter_card a b c T₁ T₃ w₁ w₃ hT1_eq hT3_eq hc_not_T1 hb_not_T3
        · rw [inter_comm]; exact T2_T3_inter_card a b c T₂ T₃ w₂ w₃ hT2_eq hT3_eq ha_not_T2 hb_not_T3
        -- T₃ vs B, C, D
        · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hB_ne' : B ≠ {a, c, b} := by rw [h_acb]; exact hB_ne
          exact hT3_disjoint B hB hB_ne'
        · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hC_ne' : C ≠ {a, c, b} := by rw [h_acb]; exact hC_ne
          exact hT3_disjoint C hC hC_ne'
        · have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hD_ne' : D ≠ {a, c, b} := by rw [h_acb]; exact hD_ne
          exact hT3_disjoint D hD hD_ne'
        -- B vs T₁, T₂, T₃
        · rw [inter_comm]; exact hT1_disjoint B hB hB_ne
        · rw [inter_comm]
          have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hB_ne' : B ≠ {b, c, a} := by rw [h_bca]; exact hB_ne
          exact hT2_disjoint B hB hB_ne'
        · rw [inter_comm]
          have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hB_ne' : B ≠ {a, c, b} := by rw [h_acb]; exact hB_ne
          exact hT3_disjoint B hB hB_ne'
        -- B vs C, D (from M packing)
        · exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
        · exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
        -- C vs T₁, T₂, T₃
        · rw [inter_comm]; exact hT1_disjoint C hC hC_ne
        · rw [inter_comm]
          have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hC_ne' : C ≠ {b, c, a} := by rw [h_bca]; exact hC_ne
          exact hT2_disjoint C hC hC_ne'
        · rw [inter_comm]
          have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hC_ne' : C ≠ {a, c, b} := by rw [h_acb]; exact hC_ne
          exact hT3_disjoint C hC hC_ne'
        -- C vs B, D
        · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hC (by simp [mem_coe]) hBC
        · exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
        -- D vs T₁, T₂, T₃
        · rw [inter_comm]; exact hT1_disjoint D hD hD_ne
        · rw [inter_comm]
          have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hD_ne' : D ≠ {b, c, a} := by rw [h_bca]; exact hD_ne
          exact hT2_disjoint D hD hD_ne'
        · rw [inter_comm]
          have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
          have hD_ne' : D ≠ {a, c, b} := by rw [h_acb]; exact hD_ne
          exact hT3_disjoint D hD hD_ne'
        -- D vs B, C
        · rw [inter_comm]; exact hM.2 hB (by simp [mem_coe]) hD (by simp [mem_coe]) hBD
        · rw [inter_comm]; exact hM.2 hC (by simp [mem_coe]) hD (by simp [mem_coe]) hCD
    -- Show S.card = 6, contradicting ν = 4
    have hS_card_6 : S.card = 6 := by
      simp only [S]
      have hT1_ne_T2 : T₁ ≠ T₂ := by
        intro heq
        rw [hT1_eq, hT2_eq] at heq
        have ha_in : a ∈ ({a, b, w₁} : Finset V) := by simp
        rw [heq] at ha_in
        simp only [mem_insert, mem_singleton] at ha_in
        rcases ha_in with rfl | rfl | rfl
        · exact hab rfl
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
        have h_inter_le : (B ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hB_ne
          exact hM.2 hB (by simp [mem_coe]) hE (by simp [mem_coe]) hB_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT1_ne_C : T₁ ≠ C := by
        intro heq
        have h_inter_ge : (T₁ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se
          exact hT1_Se.1.2
        have h_inter_le : (C ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hC_ne
          exact hM.2 hC (by simp [mem_coe]) hE (by simp [mem_coe]) hC_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT1_ne_D : T₁ ≠ D := by
        intro heq
        have h_inter_ge : (T₁ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT1_Se
          exact hT1_Se.1.2
        have h_inter_le : (D ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hD_ne
          exact hM.2 hD (by simp [mem_coe]) hE (by simp [mem_coe]) hD_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT2_ne_B : T₂ ≠ B := by
        intro heq
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have h_inter_ge : (T₂ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT2_Se_raw
          rw [h_bca] at hT2_Se_raw
          exact hT2_Se_raw.1.2
        have h_inter_le : (B ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hB_ne
          exact hM.2 hB (by simp [mem_coe]) hE (by simp [mem_coe]) hB_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT2_ne_C : T₂ ≠ C := by
        intro heq
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have h_inter_ge : (T₂ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT2_Se_raw
          rw [h_bca] at hT2_Se_raw
          exact hT2_Se_raw.1.2
        have h_inter_le : (C ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hC_ne
          exact hM.2 hC (by simp [mem_coe]) hE (by simp [mem_coe]) hC_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT2_ne_D : T₂ ≠ D := by
        intro heq
        have h_bca : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have h_inter_ge : (T₂ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT2_Se_raw
          rw [h_bca] at hT2_Se_raw
          exact hT2_Se_raw.1.2
        have h_inter_le : (D ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hD_ne
          exact hM.2 hD (by simp [mem_coe]) hE (by simp [mem_coe]) hD_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT3_ne_B : T₃ ≠ B := by
        intro heq
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have h_inter_ge : (T₃ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT3_Se_raw
          rw [h_acb] at hT3_Se_raw
          exact hT3_Se_raw.1.2
        have h_inter_le : (B ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hB_ne
          exact hM.2 hB (by simp [mem_coe]) hE (by simp [mem_coe]) hB_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT3_ne_C : T₃ ≠ C := by
        intro heq
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have h_inter_ge : (T₃ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT3_Se_raw
          rw [h_acb] at hT3_Se_raw
          exact hT3_Se_raw.1.2
        have h_inter_le : (C ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hC_ne
          exact hM.2 hC (by simp [mem_coe]) hE (by simp [mem_coe]) hC_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      have hT3_ne_D : T₃ ≠ D := by
        intro heq
        have h_acb : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
        have h_inter_ge : (T₃ ∩ {a, b, c}).card ≥ 2 := by
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT3_Se_raw
          rw [h_acb] at hT3_Se_raw
          exact hT3_Se_raw.1.2
        have h_inter_le : (D ∩ {a, b, c}).card ≤ 1 := by
          rw [hE_eq] at hD_ne
          exact hM.2 hD (by simp [mem_coe]) hE (by simp [mem_coe]) hD_ne
        rw [heq, hE_eq] at h_inter_ge
        omega
      rw [card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem,
          card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
      all_goals simp_all
    have h_bound := hNu4 S hS_packing
    omega
  -- Now case split: at least one edge type is empty
  push_neg at h_not_all_three
  rcases h_not_all_three with h_ab_empty | h_bc_empty | h_ac_empty
  -- Case 1: S_e^{a,b} empty → use {s(b,c), s(a,c)}
  · use {s(b, c), s(a, c)}
    refine ⟨?_, ?_, ?_⟩
    · intro e he; simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · simp only [card_insert_of_not_mem, card_singleton]; omega
      simp only [mem_singleton, Sym2.eq_iff]; push_neg
      constructor <;> intro h; exact hbc h.symm; exact hac.symm h.1
    · intro T hT
      simp only [mem_insert] at hT
      rcases hT with rfl | hT_Se
      · use s(b, c); simp only [mem_insert, true_or, and_true]
        rw [hE_eq]; apply edge_covers_triangle <;> simp
      · rw [hE_eq] at hT_Se
        have h_shares := Se_external_shares_edge G M a b c hab hbc hac T hT_Se
        rcases h_shares with ⟨ha_T, hb_T⟩ | ⟨hb_T, hc_T⟩ | ⟨ha_T, hc_T⟩
        · exfalso; apply h_ab_empty
          simp only [S_e_edge, mem_filter]
          refine ⟨hT_Se, ha_T, hb_T, ?_⟩
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se
          obtain ⟨⟨hT_clique, _⟩, hT_ne, _⟩ := hT_Se
          have hT_card : T.card = 3 := by
            rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique; exact hT_clique.2
          intro hc_T
          have hT_eq : T = {a, b, c} := by
            apply eq_of_subset_of_card_le
            · intro x hx; simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            · rw [hT_card, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
              · simp [hbc]
              · simp [hab, hac]
          exact hT_ne hT_eq
        · use s(b, c); simp only [mem_insert, true_or, and_true]
          exact edge_covers_triangle T b c hb_T hc_T
        · use s(a, c); simp only [mem_insert, mem_singleton, or_true, and_true]
          exact edge_covers_triangle T a c ha_T hc_T
  -- Case 2: S_e^{b,c} empty → use {s(a,b), s(a,c)}
  · use {s(a, b), s(a, c)}
    refine ⟨?_, ?_, ?_⟩
    · intro e he; simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · simp only [card_insert_of_not_mem, card_singleton]; omega
      simp only [mem_singleton, Sym2.eq_iff]; push_neg
      constructor <;> intro h; exact hab h.1; exact hac h.1
    · intro T hT
      simp only [mem_insert] at hT
      rcases hT with rfl | hT_Se
      · use s(a, b); simp only [mem_insert, true_or, and_true]
        rw [hE_eq]; apply edge_covers_triangle <;> simp
      · rw [hE_eq] at hT_Se
        have h_shares := Se_external_shares_edge G M a b c hab hbc hac T hT_Se
        rcases h_shares with ⟨ha_T, hb_T⟩ | ⟨hb_T, hc_T⟩ | ⟨ha_T, hc_T⟩
        · use s(a, b); simp only [mem_insert, true_or, and_true]
          exact edge_covers_triangle T a b ha_T hb_T
        · exfalso; apply h_bc_empty
          simp only [S_e_edge, mem_filter]
          refine ⟨?_, hb_T, hc_T, ?_⟩
          · simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se ⊢
            have h_eq : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
            rw [h_eq]; exact hT_Se
          · simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se
            obtain ⟨⟨hT_clique, _⟩, hT_ne, _⟩ := hT_Se
            have hT_card : T.card = 3 := by
              rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique; exact hT_clique.2
            intro ha_T
            have hT_eq : T = {a, b, c} := by
              apply eq_of_subset_of_card_le
              · intro x hx; simp only [mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              · rw [hT_card, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
                · simp [hbc]
                · simp [hab, hac]
            exact hT_ne hT_eq
        · use s(a, c); simp only [mem_insert, mem_singleton, or_true, and_true]
          exact edge_covers_triangle T a c ha_T hc_T
  -- Case 3: S_e^{a,c} empty → use {s(a,b), s(b,c)}
  · use {s(a, b), s(b, c)}
    refine ⟨?_, ?_, ?_⟩
    · intro e he; simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · simp only [card_insert_of_not_mem, card_singleton]; omega
      simp only [mem_singleton, Sym2.eq_iff]; push_neg
      constructor <;> intro h; exact hab h.1; exact hbc.symm h.2
    · intro T hT
      simp only [mem_insert] at hT
      rcases hT with rfl | hT_Se
      · use s(a, b); simp only [mem_insert, true_or, and_true]
        rw [hE_eq]; apply edge_covers_triangle <;> simp
      · rw [hE_eq] at hT_Se
        have h_shares := Se_external_shares_edge G M a b c hab hbc hac T hT_Se
        rcases h_shares with ⟨ha_T, hb_T⟩ | ⟨hb_T, hc_T⟩ | ⟨ha_T, hc_T⟩
        · use s(a, b); simp only [mem_insert, true_or, and_true]
          exact edge_covers_triangle T a b ha_T hb_T
        · use s(b, c); simp only [mem_insert, mem_singleton, or_true, and_true]
          exact edge_covers_triangle T b c hb_T hc_T
        · exfalso; apply h_ac_empty
          simp only [S_e_edge, mem_filter]
          refine ⟨?_, ha_T, hc_T, ?_⟩
          · simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se ⊢
            have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
            rw [h_eq]; exact hT_Se
          · simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se
            obtain ⟨⟨hT_clique, _⟩, hT_ne, _⟩ := hT_Se
            have hT_card : T.card = 3 := by
              rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique; exact hT_clique.2
            intro hb_T
            have hT_eq : T = {a, b, c} := by
              apply eq_of_subset_of_card_le
              · intro x hx; simp only [mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              · rw [hT_card, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
                · simp [hbc]
                · simp [hab, hac]
            exact hT_ne hT_eq

end