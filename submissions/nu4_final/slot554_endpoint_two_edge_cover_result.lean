/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3cf195e6-615b-4461-9710-0b4b6b3f837e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot554_endpoint_two_edge_cover.lean

  ENDPOINT TWO-EDGE COVER:

  If u ∈ A = {v1, a1, a2} is a "universal apex" (every non-M triangle
  in T_e(G, A) contains u), then the 2 spoke edges from u cover all
  of T_e(G, A).

  Specifically: if u = a1, then {s(a1,v1), s(a1,a2)} covers T_e(A).
  Proof: Let T ∈ T_e(A) with |T ∩ A| ≥ 2.
    - If T = A (∈ M): s(a1,v1) ∈ A.sym2 since a1,v1 ∈ A. ✓
    - If T ∉ M: a1 ∈ T (universal apex). Since |T ∩ A| ≥ 2,
      at least one more vertex of A is in T: v1 or a2.
      If v1 ∈ T: s(a1,v1) ∈ T.sym2. ✓
      If a2 ∈ T: s(a1,a2) ∈ T.sym2. ✓

  This gives τ(T_e(A)) ≤ 2 for any endpoint with a universal apex.

  SORRY COUNT: 0
  AXIOM COUNT: 0
  TIER: 1 (elementary)
-/

import Mathlib


set_option maxHeartbeats 600000

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

def T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ e).card)

-- ═══════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma edge_in_sym2 (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  rw [Finset.mk_mem_sym2_iff]; exact ⟨ha, hb⟩

lemma clique_edge_in_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  exact SimpleGraph.mem_edgeFinset.mpr (he.2 ha hb hab)

lemma T_e_mem_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (T : Finset V) (hT : T ∈ T_e G A) :
    T ∈ G.cliqueFinset 3 := by
  simp only [T_e, mem_filter] at hT; exact hT.1

lemma T_e_inter_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (T : Finset V) (hT : T ∈ T_e G A) :
    2 ≤ (T ∩ A).card := by
  simp only [T_e, mem_filter] at hT; exact hT.2

-- ═══════════════════════════════════════════════════════════════════════
-- KEY HELPER: u ∈ T and |T ∩ {u,v,w}| ≥ 2 implies v ∈ T or w ∈ T
-- ═══════════════════════════════════════════════════════════════════════

/-- If u ∈ T and |T ∩ {u, v, w}| ≥ 2, then v ∈ T or w ∈ T. -/
lemma apex_gives_spoke (T : Finset V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w)
    (hu : u ∈ T) (h_inter : 2 ≤ (T ∩ {u, v, w}).card) :
    v ∈ T ∨ w ∈ T := by
  by_contra h; push_neg at h
  have hsub : T ∩ {u, v, w} ⊆ {u} := by
    intro x hx
    rw [mem_inter] at hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact mem_singleton.mpr rfl
    · exact absurd hx.1 h.1
    · exact absurd hx.1 h.2
  linarith [card_le_card hsub, card_singleton u]

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Universal apex gives 2-edge cover of T_e(A)
-- ═══════════════════════════════════════════════════════════════════════

/-- If u ∈ A = {u, v, w} is in every non-M triangle of T_e(A),
    then {s(u,v), s(u,w)} covers all of T_e(A). -/
theorem two_edge_cover_from_apex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    -- Element A = {u, v, w}
    (A : Finset V) (hA : A ∈ M) (u v w : V)
    (hA_eq : A = {u, v, w})
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    -- Universal apex: u is in every non-M T_e(A) triangle
    (h_apex : ∀ T ∈ T_e G A, T ∉ M → u ∈ T) :
    -- Cover edges
    let E := ({s(u, v), s(u, w)} : Finset (Sym2 V))
    -- E ⊆ G.edgeFinset
    E ⊆ G.edgeFinset ∧
    -- |E| ≤ 2
    E.card ≤ 2 ∧
    -- E covers all of T_e(A)
    (∀ T ∈ T_e G A, ∃ e ∈ E, e ∈ T.sym2) := by
  intro E
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1 hA
  rw [hA_eq] at hA_clique
  -- E ⊆ G.edgeFinset
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [E, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact clique_edge_in_edgeFinset G {u, v, w} hA_clique u v (by simp) (by simp) huv
    · exact clique_edge_in_edgeFinset G {u, v, w} hA_clique u w
        (by simp) (by simp [huv, huw]) huw
  -- |E| ≤ 2
  · simp only [E]
    have : ({s(u, v), s(u, w)} : Finset (Sym2 V)).card ≤ 2 := by
      rw [card_insert_of_not_mem, card_singleton]
      · simp only [mem_singleton]; intro h; rw [Sym2.mk_eq_mk_iff] at h
        rcases h with ⟨_, h⟩ | ⟨h, _⟩
        · exact hvw h
        · exact huw h.symm
    exact this
  -- E covers T_e(A)
  · intro T hT
    have hT_clique := T_e_mem_clique G A T hT
    have hT_inter := T_e_inter_ge_2 G A T hT
    by_cases hT_M : T ∈ M
    · -- T ∈ M: T must be A (since |T ∩ A| ≥ 2 and packing condition)
      -- Actually T could be A or share edge with A but be different.
      -- If T = A: trivially covered
      -- If T ≠ A: |T ∩ A| ≤ 1 by packing, but we have ≥ 2. Contradiction.
      have hT_eq_A : T = A := by
        by_contra hT_ne
        have := hM.2 (mem_coe.mpr hT_M) (mem_coe.mpr hA) hT_ne
        rw [hA_eq] at hT_inter
        linarith
      -- T = A, so u ∈ T and v ∈ T
      rw [hT_eq_A, hA_eq]
      exact ⟨s(u, v), by simp [E], edge_in_sym2 {u, v, w} u v (by simp) (by simp)⟩
    · -- T ∉ M: u ∈ T by universal apex
      have hu := h_apex T hT hT_M
      rw [hA_eq] at hT_inter
      rcases apex_gives_spoke T u v w huv huw hu hT_inter with hv | hw
      · exact ⟨s(u, v), by simp [E], edge_in_sym2 T u v hu hv⟩
      · exact ⟨s(u, w), by simp [E], edge_in_sym2 T u w hu hw⟩

-- ═══════════════════════════════════════════════════════════════════════
-- VARIANT: When v1 is universal (no base-edge external case)
-- ═══════════════════════════════════════════════════════════════════════

/-- When all T_e(A) triangles contain v1 (no base-edge external),
    {s(v1,a1), s(v1,a2)} covers T_e(A). -/
theorem two_edge_cover_v1_apex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (h_all_v1 : ∀ T ∈ T_e G A, T ∉ M → v1 ∈ T) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ T ∈ T_e G A, ∃ e ∈ E, e ∈ T.sym2 := by
  have ⟨h1, h2, h3⟩ := two_edge_cover_from_apex G M hM A hA v1 a1 a2
    hA_eq h12 h13 h23 h_all_v1
  exact ⟨{s(v1, a1), s(v1, a2)}, h1, h2, h3⟩

-- ═══════════════════════════════════════════════════════════════════════
-- VARIANT: When a1 is universal (base-edge external exists, bridges
-- through a1 only)
-- ═══════════════════════════════════════════════════════════════════════

/-- When a1 is universal for T_e(A), {s(a1,v1), s(a1,a2)} covers T_e(A). -/
theorem two_edge_cover_a1_apex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (h_all_a1 : ∀ T ∈ T_e G A, T ∉ M → a1 ∈ T) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ T ∈ T_e G A, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Rewrite A = {a1, v1, a2} to use a1 as first element
  have hA_eq' : A = {a1, v1, a2} := by rw [hA_eq]; ext x; simp [or_comm, or_assoc]
  have ⟨h1, h2, h3⟩ := two_edge_cover_from_apex G M hM A hA a1 v1 a2
    hA_eq' h12.symm h23 h13.symm h_all_a1
  exact ⟨{s(a1, v1), s(a1, a2)}, h1, h2, h3⟩

/-- Symmetric: when a2 is universal, {s(a2,v1), s(a2,a1)} covers T_e(A). -/
theorem two_edge_cover_a2_apex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (h_all_a2 : ∀ T ∈ T_e G A, T ∉ M → a2 ∈ T) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ T ∈ T_e G A, ∃ e ∈ E, e ∈ T.sym2 := by
  have hA_eq' : A = {a2, v1, a1} := by rw [hA_eq]; ext x; simp [or_comm, or_assoc]
  have ⟨h1, h2, h3⟩ := two_edge_cover_from_apex G M hM A hA a2 v1 a1
    hA_eq' h13.symm h23.symm h12.symm h_all_a2
  exact ⟨{s(a2, v1), s(a2, a1)}, h1, h2, h3⟩

-- ═══════════════════════════════════════════════════════════════════════
-- COMBINED: τ(T_e(A)) ≤ 2 for any endpoint with universal apex
-- ═══════════════════════════════════════════════════════════════════════

/-- For any endpoint A with a universal apex, τ(T_e(A)) ≤ 2. -/
theorem endpoint_tau_Te_le_2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    -- There exists a universal apex
    (h_apex : ∃ u ∈ ({v1, a1, a2} : Finset V), ∀ T ∈ T_e G A, T ∉ M → u ∈ T) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ T ∈ T_e G A, ∃ e ∈ E, e ∈ T.sym2 := by
  obtain ⟨u, hu_A, hu_apex⟩ := h_apex
  simp only [mem_insert, mem_singleton] at hu_A
  rcases hu_A with rfl | rfl | rfl
  · exact two_edge_cover_v1_apex G M hM A hA v1 a1 a2 hA_eq h12 h13 h23 hu_apex
  · exact two_edge_cover_a1_apex G M hM A hA v1 a1 a2 hA_eq h12 h13 h23 hu_apex
  · exact two_edge_cover_a2_apex G M hM A hA v1 a1 a2 hA_eq h12 h13 h23 hu_apex

end