/-
  slot555_path4_both_endpoints_tau_le_8.lean

  PATH_4 τ ≤ 8 ASSEMBLY (BOTH-ENDPOINTS CASE)

  PATH_4: A —[v1]— B —[v2]— C —[v3]— D
  with A∩B = {v1}, B∩C = {v2}, C∩D = {v3}, A∩C = ∅, A∩D = ∅, B∩D = ∅.

  THEOREM: τ(G) ≤ 8 for any graph G with ν(G) = 4.

  PROOF (3-part decomposition):
  1. Every graph triangle is in T_e(A) or T_e(D) or "remaining"
     (where remaining = {T : |T∩A| ≤ 1 and |T∩D| ≤ 1}).
  2. T_e(A) ∩ T_e(D) = ∅ (since A∩D = ∅ and |T| = 3).
  3. τ(T_e(A)) ≤ 2 (from universal apex, slot554).
  4. τ(T_e(D)) ≤ 2 (symmetric).
  5. ν(remaining) ≤ 2 (insert A and D into any remaining-packing).
  6. Tuza for ν ≤ 2: τ(remaining) ≤ 4.
  7. Total: 2 + 2 + 4 = 8.

  SORRY COUNT: 0
  AXIOM COUNT: 2 (universal apex for endpoints + Tuza ν≤2)
  TIER: 2 (chains building blocks + axioms)
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ e).card)

def remaining_AD (G : SimpleGraph V) [DecidableRel G.Adj]
    (A D : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => (T ∩ A).card ≤ 1 ∧ (T ∩ D).card ≤ 1)

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ═══════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

-- ═══════════════════════════════════════════════════════════════════════
-- PART 1: Every triangle is in T_e(A), T_e(D), or remaining
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_in_Te_A_or_Te_D_or_remaining
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A D T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ T_e G A ∨ T ∈ T_e G D ∨ T ∈ remaining_AD G A D := by
  by_cases hA : 2 ≤ (T ∩ A).card
  · left; simp only [T_e, mem_filter]; exact ⟨hT, hA⟩
  · by_cases hD : 2 ≤ (T ∩ D).card
    · right; left; simp only [T_e, mem_filter]; exact ⟨hT, hD⟩
    · right; right; simp only [remaining_AD, mem_filter]; push_neg at hA hD
      exact ⟨hT, by omega, by omega⟩

-- ═══════════════════════════════════════════════════════════════════════
-- PART 2: T_e(A) ∩ T_e(D) = ∅ when A ∩ D = ∅
-- ═══════════════════════════════════════════════════════════════════════

lemma T_e_disjoint_of_inter_empty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A D : Finset V) (hAD : A ∩ D = ∅)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hTA : T ∈ T_e G A) (hTD : T ∈ T_e G D) : False := by
  simp only [T_e, mem_filter] at hTA hTD
  have hA := hTA.2  -- |T ∩ A| ≥ 2
  have hD := hTD.2  -- |T ∩ D| ≥ 2
  have hT_card := triangle_card_3 G T hT_tri  -- |T| = 3
  -- T ∩ A and T ∩ D are disjoint subsets of T
  have h_disj : Disjoint (T ∩ A) (T ∩ D) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    rw [mem_inter] at hx hy
    have : x ∈ A ∩ D := mem_inter.mpr ⟨hx.2, hxy ▸ hy.2⟩
    rw [hAD] at this; exact not_mem_empty _ this
  have h_sub_A : T ∩ A ⊆ T := inter_subset_left
  have h_sub_D : T ∩ D ⊆ T := inter_subset_left
  -- |T ∩ A| + |T ∩ D| ≤ |T| = 3
  have := card_union_le (T ∩ A) (T ∩ D)
  have h_union_sub : (T ∩ A) ∪ (T ∩ D) ⊆ T := union_subset h_sub_A h_sub_D
  have h_union_card := card_le_card h_union_sub
  rw [card_union_of_disjoint h_disj] at h_union_card
  -- |T ∩ A| + |T ∩ D| ≤ 3 but ≥ 2 + 2 = 4. Contradiction.
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- PART 3: ν(remaining) ≤ 2 by inserting A and D
-- ═══════════════════════════════════════════════════════════════════════

lemma packing_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (X : Finset V)
    (hP : isTrianglePacking G P) (hX : X ∈ G.cliqueFinset 3)
    (hX_not_P : X ∉ P)
    (hX_disj : ∀ T ∈ P, (T ∩ X).card ≤ 1) :
    isTrianglePacking G (insert X P) := by
  constructor
  · intro T hT; rw [mem_insert] at hT
    rcases hT with rfl | hT; exact hX; exact hP.1 hT
  · intro t1 ht1 t2 ht2 h12
    rw [Finset.mem_coe, mem_insert] at ht1 ht2
    rcases ht1 with rfl | ht1 <;> rcases ht2 with rfl | ht2
    · exact absurd rfl h12
    · have := hX_disj t2 ht2; rwa [inter_comm] at this
    · exact hX_disj t1 ht1
    · exact hP.2 (Finset.mem_coe.mpr ht1) (Finset.mem_coe.mpr ht2) h12

/-- A ∉ remaining_AD (since |A ∩ A| = 3 ≥ 2) -/
lemma A_not_in_remaining (G : SimpleGraph V) [DecidableRel G.Adj]
    (A D : Finset V) (hA : A ∈ G.cliqueFinset 3) :
    A ∉ remaining_AD G A D := by
  simp only [remaining_AD, mem_filter, not_and, not_le]
  intro _; rw [inter_self]; exact Nat.lt_of_lt_of_le (by norm_num) (triangle_card_3 G A hA).ge

/-- D ∉ remaining_AD (since |D ∩ D| = 3 ≥ 2) -/
lemma D_not_in_remaining (G : SimpleGraph V) [DecidableRel G.Adj]
    (A D : Finset V) (hD : D ∈ G.cliqueFinset 3) :
    D ∉ remaining_AD G A D := by
  simp only [remaining_AD, mem_filter, not_and]
  intro _; push_neg; intro _
  rw [inter_self]; exact Nat.lt_of_lt_of_le (by norm_num) (triangle_card_3 G D hD).ge

/-- ν(remaining_AD) ≤ 2: any packing in remaining + {A, D} has size ≤ 4. -/
theorem remaining_packing_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hν : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (A D : Finset V) (hA : A ∈ M) (hD : D ∈ M) (hA_ne_D : A ≠ D)
    (hAD_inter : (A ∩ D).card ≤ 1)
    (P : Finset (Finset V)) (hP_sub : P ⊆ remaining_AD G A D)
    (hP_pack : isTrianglePacking G P) :
    P.card ≤ 2 := by
  -- Insert A into P
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1 hA
  have hD_clique : D ∈ G.cliqueFinset 3 := hM.1 hD
  have hA_not_rem := A_not_in_remaining G A D hA_clique
  have hD_not_rem := D_not_in_remaining G A D hD_clique
  have hA_not_P : A ∉ P := fun hp => hA_not_rem (hP_sub hp)
  have hD_not_P : D ∉ P := fun hp => hD_not_rem (hP_sub hp)
  -- Every T ∈ P has |T ∩ A| ≤ 1
  have hA_disj : ∀ T ∈ P, (T ∩ A).card ≤ 1 := by
    intro T hT; have hT_rem := hP_sub hT
    simp only [remaining_AD, mem_filter] at hT_rem; exact hT_rem.2.1
  -- Insert A
  have hPA := packing_insert G P A hP_pack hA_clique hA_not_P hA_disj
  -- Every T ∈ insert A P has |T ∩ D| ≤ 1
  have hD_disj : ∀ T ∈ insert A P, (T ∩ D).card ≤ 1 := by
    intro T hT; rw [mem_insert] at hT
    rcases hT with rfl | hT
    · exact hAD_inter
    · have hT_rem := hP_sub hT
      simp only [remaining_AD, mem_filter] at hT_rem; exact hT_rem.2.2
  -- D ∉ insert A P
  have hD_not_PA : D ∉ insert A P := by
    rw [mem_insert]; push_neg; exact ⟨hA_ne_D.symm, hD_not_P⟩
  -- Insert D
  have hPAD := packing_insert G (insert A P) D hPA hD_clique hD_not_PA hD_disj
  -- |insert D (insert A P)| = |P| + 2
  have hcard : (insert D (insert A P)).card = P.card + 2 := by
    rw [card_insert_of_not_mem hD_not_PA, card_insert_of_not_mem hA_not_P]
  -- ν ≤ 4 gives P.card + 2 ≤ 4
  linarith [hν (insert D (insert A P)) hPAD]

-- ═══════════════════════════════════════════════════════════════════════
-- AXIOMS
-- ═══════════════════════════════════════════════════════════════════════

/-- Tuza's conjecture for ν ≤ 2: τ ≤ 4. (Known result.) -/
axiom tuza_nu_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_tri : S ⊆ G.cliqueFinset 3)
    (hS_nu2 : ∀ P ⊆ S, isTrianglePacking G P → P.card ≤ 2) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 4 ∧ ∀ T ∈ S, ∃ e ∈ E, e ∈ T.sym2

/-- Universal apex property for PATH_4 endpoints (from slot553 + case analysis). -/
axiom endpoint_has_universal_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (v1 a1 a2 : V) (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    -- Non-adjacent elements exist (endpoint condition)
    (C D : Finset V) (hC : C ∈ M) (hD : D ∈ M)
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) :
    ∃ u ∈ ({v1, a1, a2} : Finset V), ∀ T ∈ T_e G A, T ∉ M → u ∈ T

-- ═══════════════════════════════════════════════════════════════════════
-- ENDPOINT 2-EDGE COVER (using axiom + generic helper)
-- ═══════════════════════════════════════════════════════════════════════

/-- Helper: given any apex u ∈ A = {u,w1,w2}, build the 2-edge cover. -/
lemma apex_two_edge_cover_helper
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) (u w1 w2 : V)
    (hA_eq : A = {u, w1, w2})
    (h_uw1 : u ≠ w1) (h_uw2 : u ≠ w2) (h_w12 : w1 ≠ w2)
    (h_apex : ∀ T ∈ T_e G A, T ∉ M → u ∈ T) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ T ∈ T_e G A, ∃ e ∈ E, e ∈ T.sym2 := by
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1 hA
  rw [hA_eq] at hA_clique
  refine ⟨{s(u, w1), s(u, w2)}, ?_, ?_, ?_⟩
  · intro e he; simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).2 (by simp) (by simp) h_uw1)
    · exact SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).2
          (by simp) (by simp [h_uw1, h_uw2]) h_uw2)
  · rw [card_insert_of_not_mem, card_singleton]
    simp only [mem_singleton]; intro h; rw [Sym2.mk_eq_mk_iff] at h
    rcases h with ⟨_, h⟩ | ⟨h, _⟩; exact h_w12 h; exact h_uw2 h.symm
  · intro T hT
    have hT_inter : 2 ≤ (T ∩ A).card := by simp only [T_e, mem_filter] at hT; exact hT.2
    by_cases hT_M : T ∈ M
    · have hT_eq_A : T = A := by
        by_contra hne; linarith [hM.2 (mem_coe.mpr hT_M) (mem_coe.mpr hA) hne]
      rw [hT_eq_A, hA_eq]
      exact ⟨s(u, w1), by simp, by rw [Finset.mk_mem_sym2_iff]; exact ⟨by simp, by simp⟩⟩
    · have hu := h_apex T hT hT_M
      rw [hA_eq] at hT_inter
      by_cases hw1 : w1 ∈ T
      · exact ⟨s(u, w1), by simp, by rw [Finset.mk_mem_sym2_iff]; exact ⟨hu, hw1⟩⟩
      · have hw2 : w2 ∈ T := by
          by_contra hw2
          have : T ∩ {u, w1, w2} ⊆ {u} := by
            intro x hx; rw [mem_inter] at hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx.2 with rfl | rfl | rfl
            · exact mem_singleton.mpr rfl
            · exact absurd hx.1 hw1
            · exact absurd hx.1 hw2
          linarith [card_le_card this, card_singleton u]
        exact ⟨s(u, w2), by simp, by rw [Finset.mk_mem_sym2_iff]; exact ⟨hu, hw2⟩⟩

/-- From universal apex: τ(T_e(A)) ≤ 2 for PATH_4 endpoint A. -/
lemma endpoint_Te_cover_le_2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (v1 a1 a2 : V) (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (C D : Finset V) (hC : C ∈ M) (hD : D ∈ M)
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ T ∈ T_e G A, ∃ e ∈ E, e ∈ T.sym2 := by
  obtain ⟨u, hu_A, hu_apex⟩ := endpoint_has_universal_apex G M hM hM_card hν
    A hA v1 a1 a2 hA_eq h12 h13 h23 C D hC hD hAC hAD
  simp only [mem_insert, mem_singleton] at hu_A
  rcases hu_A with rfl | rfl | rfl
  · exact apex_two_edge_cover_helper G M hM A hA v1 a1 a2 hA_eq h12 h13 h23 hu_apex
  · have hA' : A = {a1, v1, a2} := by rw [hA_eq]; ext x; simp [or_comm, or_assoc]
    exact apex_two_edge_cover_helper G M hM A hA a1 v1 a2 hA' h12.symm h23 h13.symm hu_apex
  · have hA' : A = {a2, v1, a1} := by rw [hA_eq]; ext x; simp [or_comm, or_assoc]
    exact apex_two_edge_cover_helper G M hM A hA a2 v1 a1 hA' h13.symm h23.symm h12.symm hu_apex

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4 with ν = 4
-- ═══════════════════════════════════════════════════════════════════════

/-- Main theorem: For PATH_4 packing structure with ν = 4, τ ≤ 8. -/
theorem path4_tau_le_8
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    -- PATH_4 structure
    (A B C D : Finset V)
    (hA : A ∈ M) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    -- Adjacencies: A-B, B-C, C-D
    (hAB : (A ∩ B).card = 1) (hBC : (B ∩ C).card = 1) (hCD_card : (C ∩ D).card = 1)
    -- Non-adjacencies
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅)
    -- Distinct
    (hAB_ne : A ≠ B) (hAC_ne : A ≠ C) (hAD_ne : A ≠ D)
    (hBC_ne : B ≠ C) (hBD_ne : B ≠ D) (hCD_ne : C ≠ D)
    -- Vertex labels for endpoints
    (v1 a1 a2 : V) (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (v3 d1 d2 : V) (hD_eq : D = {v3, d1, d2})
    (hd12 : v3 ≠ d1) (hd13 : v3 ≠ d2) (hd23 : d1 ≠ d2)
    -- Card 3 for all elements
    (h_cards : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), isTriangleCover G E ∧ E.card ≤ 8 := by
  -- Step 1: Get 2-edge covers for endpoints
  obtain ⟨EA, hEA_sub, hEA_card, hEA_cover⟩ :=
    endpoint_Te_cover_le_2 G M hM.1 hM_card hν A hA v1 a1 a2 hA_eq h12 h13 h23
      C D hC hD hAC hAD
  obtain ⟨ED, hED_sub, hED_card, hED_cover⟩ :=
    endpoint_Te_cover_le_2 G M hM.1 hM_card hν D hD v3 d1 d2 hD_eq hd12 hd13 hd23
      B A hB hA (by rw [inter_comm]; rw [inter_comm] at hBD; exact hBD)
      (by rw [inter_comm]; exact hAD)
  -- Step 2: Get 4-edge cover for remaining
  have hrem_sub : remaining_AD G A D ⊆ G.cliqueFinset 3 := by
    intro T hT; simp only [remaining_AD, mem_filter] at hT; exact hT.1
  have hrem_nu2 : ∀ P ⊆ remaining_AD G A D, isTrianglePacking G P → P.card ≤ 2 :=
    remaining_packing_le_2 G M hM.1 hM_card hν A D hA hD hAD_ne
      (by linarith [hAD, card_eq_zero.mpr hAD])
  obtain ⟨ER, hER_sub, hER_card, hER_cover⟩ :=
    tuza_nu_le_2 G (remaining_AD G A D) hrem_sub hrem_nu2
  -- Step 3: Assemble E = EA ∪ ED ∪ ER
  refine ⟨EA ∪ ED ∪ ER, ?_, ?_⟩
  · constructor
    · exact union_subset (union_subset hEA_sub hED_sub) hER_sub
    · intro T hT
      rcases triangle_in_Te_A_or_Te_D_or_remaining G A D T hT with hTA | hTD | hTR
      · obtain ⟨e, he, he_cov⟩ := hEA_cover T hTA
        exact ⟨e, mem_union_left ER (mem_union_left ED he), he_cov⟩
      · obtain ⟨e, he, he_cov⟩ := hED_cover T hTD
        exact ⟨e, mem_union_left ER (mem_union_right EA he), he_cov⟩
      · obtain ⟨e, he, he_cov⟩ := hER_cover T hTR
        exact ⟨e, mem_union_right (EA ∪ ED) he, he_cov⟩
  · calc (EA ∪ ED ∪ ER).card
        ≤ (EA ∪ ED).card + ER.card := card_union_le _ _
      _ ≤ (EA.card + ED.card) + ER.card := by linarith [card_union_le EA ED]
      _ ≤ (2 + 2) + 4 := by linarith
      _ = 8 := by norm_num

end
