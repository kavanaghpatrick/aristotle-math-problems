/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f21fa40e-38a4-43e8-a1fe-9e2f377f38a5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot544_endpoint_no_base_external.lean

  THEOREM: If A = {v1, a1, a2} is a triangle in G such that every triangle
  sharing an edge with A contains vertex v1, then 2 edges cover all of T_e(A).

  APPLICATION: In PATH_4, if endpoint A has no base-edge external
  (no S_A triangle uses edge {a1,a2}), then all T_A triangles contain v1.
  Combined with bridge_contains_shared_vertex, this gives τ(T_A) ≤ 2.
  Then Parker's Lemma 2.3 gives τ ≤ 2 + 3·g₃ = 2 + 6 = 8.

  TIER: 1-2 (set theory + explicit edge construction)
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

/-- T_e: all graph triangles sharing an edge (≥2 vertices) with e -/
def T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ e).card)

-- ═══════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.1.card_eq

lemma clique_edge_in_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  exact SimpleGraph.mem_edgeFinset.mpr (he.2 ha hb hab)

lemma edge_in_sym2 (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  rw [Finset.mk_mem_sym2_iff]; exact ⟨ha, hb⟩

/-- T_e elements share ≥ 2 vertices with e -/
lemma T_e_inter_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e T : Finset V) (hT : T ∈ T_e G e) :
    2 ≤ (T ∩ e).card := by
  simp only [T_e, mem_filter] at hT; exact hT.2

/-- T_e elements are graph triangles -/
lemma T_e_mem_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (e T : Finset V) (hT : T ∈ T_e G e) :
    T ∈ G.cliqueFinset 3 := by
  simp only [T_e, mem_filter] at hT; exact hT.1

/-- Card of {v1, a1, a2} when all distinct -/
lemma card_triple (v1 a1 a2 : V) (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2) :
    ({v1, a1, a2} : Finset V).card = 3 := by
  rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
  · exact fun h => h23 (mem_singleton.mp h)
  · simp only [mem_insert, mem_singleton]
    push_neg; exact ⟨h12, h13⟩

/-- Two distinct Sym2 elements from v1 to different vertices -/
lemma sym2_pair_ne (v1 a1 a2 : V) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2) :
    s(v1, a1) ≠ s(v1, a2) := by
  intro h
  rw [Sym2.mk_eq_mk_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h23 h
  · exact h13 h.symm

/-- Card of 2-element Sym2 finset -/
lemma card_sym2_pair (v1 a1 a2 : V) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2) :
    ({s(v1, a1), s(v1, a2)} : Finset (Sym2 V)).card = 2 := by
  rw [card_insert_of_not_mem, card_singleton]
  simp only [mem_singleton]
  exact sym2_pair_ne v1 a1 a2 h13 h23

/-- If v1 ∈ T and |T ∩ {v1,a1,a2}| ≥ 2, then a1 ∈ T or a2 ∈ T -/
lemma v1_mem_inter_ge_2_gives_base (T : Finset V) (v1 a1 a2 : V)
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2)
    (hv1 : v1 ∈ T) (h_inter : 2 ≤ (T ∩ {v1, a1, a2}).card) :
    a1 ∈ T ∨ a2 ∈ T := by
  by_contra h; push_neg at h
  have hsub : T ∩ {v1, a1, a2} ⊆ {v1} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact mem_singleton.mpr rfl
    · exact absurd hx.1 h.1
    · exact absurd hx.1 h.2
  have : (T ∩ {v1, a1, a2}).card ≤ 1 :=
    (card_le_card hsub).trans (card_singleton v1).le
  omega

/-- The pair {s(v1,a1), s(v1,a2)} is a subset of G.edgeFinset when A is a clique -/
lemma cover_pair_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (v1 a1 a2 : V) (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (hA : {v1, a1, a2} ∈ G.cliqueFinset 3) :
    ({s(v1, a1), s(v1, a2)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
  intro e he
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact clique_edge_in_edgeFinset G {v1, a1, a2} hA v1 a1
      (by simp) (by simp) h12
  · exact clique_edge_in_edgeFinset G {v1, a1, a2} hA v1 a2
      (by simp) (by simp [h12, h13]) h13

/-- Each T_e triangle containing v1 is covered by s(v1,a1) or s(v1,a2) -/
lemma triangle_covered_by_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (v1 a1 a2 : V) (h12 : v1 ≠ a1) (h13 : v1 ≠ a2)
    (A : Finset V) (hA_eq : A = {v1, a1, a2})
    (T : Finset V) (hv1 : v1 ∈ T) (h_inter : 2 ≤ (T ∩ A).card) :
    ∃ edge ∈ ({s(v1, a1), s(v1, a2)} : Finset (Sym2 V)), edge ∈ T.sym2 := by
  rw [hA_eq] at h_inter
  rcases v1_mem_inter_ge_2_gives_base T v1 a1 a2 h12 h13 hv1 h_inter with ha1 | ha2
  · exact ⟨s(v1, a1), by simp, edge_in_sym2 T v1 a1 hv1 ha1⟩
  · exact ⟨s(v1, a2), by simp, edge_in_sym2 T v1 a2 hv1 ha2⟩

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
Given A = {v1, a1, a2} a clique in G, and the hypothesis that every triangle
sharing an edge with A contains vertex v1:

1. Define E = {s(v1,a1), s(v1,a2)}.
2. E ⊆ G.edgeFinset: by cover_pair_subset_edgeFinset (A is a clique in G).
3. E.card ≤ 2: by card_sym2_pair (since a1 ≠ a2 and v1 ≠ a2).
4. For any T ∈ T_e(G,A):
   a. T is a graph triangle with |T ∩ A| ≥ 2 (by T_e_inter_ge_2)
   b. v1 ∈ T (by hypothesis h_all_v1)
   c. Since v1 ∈ T and |T ∩ {v1,a1,a2}| ≥ 2, either a1 ∈ T or a2 ∈ T
      (by v1_mem_inter_ge_2_gives_base)
   d. If a1 ∈ T: s(v1,a1) ∈ T.sym2 covers T (by edge_in_sym2)
      If a2 ∈ T: s(v1,a2) ∈ T.sym2 covers T (by edge_in_sym2)
5. Use triangle_covered_by_pair to close each case.
6. Conclude: E has ≤ 2 edges, all in G.edgeFinset, covering all of T_e(G,A).
-/
theorem endpoint_tau_le_2_when_all_contain_v1
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hA : A ∈ G.cliqueFinset 3)
    (v1 a1 a2 : V) (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    -- Key hypothesis: every triangle sharing edge with A contains v1
    (h_all_v1 : ∀ T ∈ T_e G A, v1 ∈ T) :
    ∃ E : Finset (Sym2 V),
      E ⊆ G.edgeFinset ∧
      E.card ≤ 2 ∧
      ∀ T ∈ T_e G A, ∃ edge ∈ E, edge ∈ T.sym2 := by
  refine ⟨{s(v1, a1), s(v1, a2)}, ?_, ?_, ?_⟩
  · -- E ⊆ G.edgeFinset
    rw [hA_eq] at hA
    exact cover_pair_subset_edgeFinset G v1 a1 a2 h12 h13 h23 hA
  · -- E.card ≤ 2
    exact (card_sym2_pair v1 a1 a2 h13 h23).le
  · -- Covers all T_e
    intro T hT
    exact triangle_covered_by_pair G v1 a1 a2 h12 h13 A hA_eq T
      (h_all_v1 T hT) (T_e_inter_ge_2 G A T hT)

-- ═══════════════════════════════════════════════════════════════════════
-- COROLLARY: No base-edge external → v1 in all T_e
-- (Needed to connect the hypothesis to PATH_4 structure)
-- ═══════════════════════════════════════════════════════════════════════

/-- If |T ∩ {v1,a1,a2}| ≥ 2 and T doesn't use base-edge {a1,a2} without v1,
    then v1 ∈ T -/
lemma no_base_edge_implies_v1_mem (T : Finset V) (v1 a1 a2 : V)
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (h_inter : 2 ≤ (T ∩ {v1, a1, a2}).card)
    (h_no_base : ¬(a1 ∈ T ∧ a2 ∈ T ∧ v1 ∉ T)) :
    v1 ∈ T := by
  by_contra hv1
  -- Since v1 ∉ T, T ∩ {v1,a1,a2} ⊆ {a1,a2}
  have hsub : T ∩ {v1, a1, a2} ⊆ {a1, a2} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 hv1
    · exact mem_insert_self a1 {a2}
    · exact mem_insert_of_mem a1 (mem_singleton.mpr rfl)
  -- |T ∩ A| ≤ 2, combined with ≥ 2 gives = 2, so T ∩ A = {a1, a2}
  have hcard_le : (T ∩ {v1, a1, a2}).card ≤ ({a1, a2} : Finset V).card :=
    card_le_card hsub
  have hcard_pair : ({a1, a2} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem, card_singleton]
    exact fun h => h23 (mem_singleton.mp h)
  have h_eq_card : (T ∩ {v1, a1, a2}).card = 2 := by omega
  have h_eq_set : T ∩ {v1, a1, a2} = {a1, a2} :=
    eq_of_subset_of_card_le hsub (by rw [h_eq_card, hcard_pair])
  -- So a1, a2 ∈ T
  have ha1 : a1 ∈ T := by
    have : a1 ∈ T ∩ {v1, a1, a2} := h_eq_set ▸ mem_insert_self a1 {a2}
    exact mem_of_mem_inter_left this
  have ha2 : a2 ∈ T := by
    have : a2 ∈ T ∩ {v1, a1, a2} :=
      h_eq_set ▸ mem_insert_of_mem a1 (mem_singleton.mpr rfl)
    exact mem_of_mem_inter_left this
  -- But h_no_base says ¬(a1 ∈ T ∧ a2 ∈ T ∧ v1 ∉ T)
  exact h_no_base ⟨ha1, ha2, hv1⟩

end