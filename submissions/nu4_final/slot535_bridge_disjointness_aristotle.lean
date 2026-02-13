/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 45829c4f-2c0e-479d-a38a-66abc7808e1b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot535: BRIDGE DISJOINTNESS LEMMA

  KEY HELPER: Prove that if apex is away from bridge, the selected
  apex-edges are disjoint from the bridge's shared edge.

  This is a critical step in the exchange argument.
-/

import Mathlib


set_option maxHeartbeats 400000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma triangle_card_eq_three (T : Finset V) (hT : T.card = 3) :
    ∃ a b c : V, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ T = {a, b, c} := by
  obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := Finset.card_eq_three.mp hT
  exact ⟨a, b, c, by rw [h_eq]; simp, by rw [h_eq]; simp, by rw [h_eq]; simp,
         hab, hac, hbc, h_eq⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- APEX EDGE DISJOINTNESS
-- ══════════════════════════════════════════════════════════════════════════════

/-- If X = {apex, u, v} with apex ∉ Br and {u,v} ⊆ Br,
    then apex-edges {apex, u} and {apex, v} are disjoint from Br's edges -/
lemma apex_edges_disjoint_from_bridge (X Br : Finset V)
    (hX_card : X.card = 3) (hBr_card : Br.card = 3)
    (apex : V) (u v : V)
    (h_X_eq : X = {apex, u, v})
    (h_apex_not_Br : apex ∉ Br)
    (h_u_in_Br : u ∈ Br) (h_v_in_Br : v ∈ Br)
    (h_distinct : apex ≠ u ∧ apex ≠ v ∧ u ≠ v) :
    -- The apex-edges do NOT coincide with any edge of Br (except {u,v})
    ∀ e ∈ Br.sym2, (e = s(apex, u) ∨ e = s(apex, v)) → e = s(u, v) → False := by
  intro e he h_apex_edge h_uv
  -- If e is an apex-edge, it contains apex
  -- If e = s(u,v), it doesn't contain apex (since apex ≠ u, apex ≠ v)
  rcases h_apex_edge with rfl | rfl
  · -- e = s(apex, u) and e = s(u, v)
    have h_eq : s(apex, u) = s(u, v) := h_uv
    simp only [Sym2.eq_iff] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h_distinct.2.1 rfl
    · exact h_distinct.1 rfl
  · -- e = s(apex, v) and e = s(u, v)
    have h_eq : s(apex, v) = s(u, v) := h_uv
    simp only [Sym2.eq_iff] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h_distinct.1 rfl
    · exact h_distinct.2.1 rfl

/-- The apex-edges from X don't share the edge with Br (the base edge) -/
lemma apex_selection_not_bridge_edge (X Br : Finset V)
    (hX_card : X.card = 3) (hBr_card : Br.card = 3)
    (h_share : (X ∩ Br).card = 2)
    (apex : V) (h_apex_in_X : apex ∈ X) (h_apex_not_Br : apex ∉ Br) :
    ∃ u v : V, u ∈ X ∧ v ∈ X ∧ u ∈ Br ∧ v ∈ Br ∧ u ≠ v ∧
              X ∩ Br = {u, v} ∧
              s(apex, u) ≠ s(u, v) ∧ s(apex, v) ≠ s(u, v) := by
  -- The shared part X ∩ Br has exactly 2 elements
  obtain ⟨u', v', huv', h_inter_eq⟩ := Finset.card_eq_two.mp h_share
  -- u', v' are in both X and Br
  have hu'_X : u' ∈ X := by
    have : u' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_self _ _
    exact Finset.mem_of_mem_inter_left this
  have hv'_X : v' ∈ X := by
    have : v' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact Finset.mem_of_mem_inter_left this
  have hu'_Br : u' ∈ Br := by
    have : u' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_self _ _
    exact Finset.mem_of_mem_inter_right this
  have hv'_Br : v' ∈ Br := by
    have : v' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact Finset.mem_of_mem_inter_right this

  use u', v', hu'_X, hv'_X, hu'_Br, hv'_Br, huv', h_inter_eq

  -- Now show apex-edges are different from {u', v'}
  have h_apex_ne_u : apex ≠ u' := by
    intro h_eq
    rw [h_eq] at h_apex_not_Br
    exact h_apex_not_Br hu'_Br
  have h_apex_ne_v : apex ≠ v' := by
    intro h_eq
    rw [h_eq] at h_apex_not_Br
    exact h_apex_not_Br hv'_Br

  constructor
  · -- s(apex, u') ≠ s(u', v')
    intro h_eq
    simp only [Sym2.eq_iff] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact h_apex_ne_v rfl; exact h_apex_ne_u rfl]
  · -- s(apex, v') ≠ s(u', v')
    intro h_eq
    simp only [Sym2.eq_iff] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact h_apex_ne_u rfl; exact h_apex_ne_v rfl]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA: If apex is away, selected edges miss the bridge base
-- ══════════════════════════════════════════════════════════════════════════════

/-- If we select edges {apex, u} and {apex, v} where apex ∉ Br,
    and {u, v} is the shared edge with Br, then neither selected edge
    is in Br.sym2 -/
lemma apex_selection_misses_bridge (X Br : Finset V)
    (hX_card : X.card = 3)
    (h_share : (X ∩ Br).card = 2)
    (apex : V) (h_apex_in_X : apex ∈ X) (h_apex_not_Br : apex ∉ Br)
    (u v : V) (h_X_eq : X = {apex, u, v}) (h_u_in_Br : u ∈ Br) (h_v_in_Br : v ∈ Br) :
    s(apex, u) ∉ Br.sym2 ∧ s(apex, v) ∉ Br.sym2 := by
  constructor
  · -- s(apex, u) ∉ Br.sym2
    intro h_in
    rw [Finset.mem_sym2_iff] at h_in
    have h1 : apex ∈ Br := h_in apex (Sym2.mem_iff.mpr (Or.inl rfl))
    exact h_apex_not_Br h1
  · -- s(apex, v) ∉ Br.sym2
    intro h_in
    rw [Finset.mem_sym2_iff] at h_in
    have h1 : apex ∈ Br := h_in apex (Sym2.mem_iff.mpr (Or.inl rfl))
    exact h_apex_not_Br h1

end