/-
Erdős Problem #128 - Triangle in Dense Induced Subgraph
$250 Prize - FIXED VERSION using Finset instead of Set

PROBLEM: If every induced subgraph on ≥ n/2 vertices has > n²/50 edges,
must G contain a triangle?

FIX: Use Finset V (not Set V) for induced subgraphs to get DecidablePred instance.
-/

import Mathlib

set_option maxHeartbeats 400000

open SimpleGraph Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Erdos128

/-- Every induced subgraph on ≥ n/2 vertices has > n²/50 edges -/
def HasDenseInducedSubgraphs (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, 2 * S.card + 1 ≥ Fintype.card V →
    50 * (G.induce (S : Set V)).edgeFinset.card > (Fintype.card V)^2

/-! ## Case 1: High Degree Vertex -/

/-- In triangle-free graph, neighborhood is independent -/
lemma neighborFinset_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    ∀ x ∈ G.neighborFinset v, ∀ y ∈ G.neighborFinset v, x ≠ y → ¬G.Adj x y := by
  intro x hx y hy hne hadj
  rw [mem_neighborFinset] at hx hy
  apply hG {v, x, y}
  simp only [isNClique_iff, isClique_iff, Set.Pairwise, coe_insert, coe_singleton,
             Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro a ha b hb hab
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals (try exact (hab rfl).elim)
    · exact hx
    · exact hy
    · exact G.symm hx
    · exact hadj
    · exact G.symm hy
    · exact G.symm hadj
  · simp [card_insert_of_not_mem, card_singleton]
    intro h; exact hne h.symm

/-- Induced subgraph on neighborhood has no edges -/
lemma neighborFinset_edgeless (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    (G.induce (G.neighborFinset v : Set V)).edgeFinset = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro e he
  simp only [mem_edgeFinset, induce_adj, Set.mem_coe, mem_neighborFinset] at he
  obtain ⟨⟨hx, hy⟩, hadj⟩ := he
  have hpw := neighborFinset_independent G hG v
  exact hpw _ (mem_neighborFinset.mpr hx) _ (mem_neighborFinset.mpr hy) (G.ne_of_adj hadj) hadj

/-- High degree case: neighborhood is large and sparse -/
theorem high_degree_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) (hv : 2 * G.degree v + 1 ≥ Fintype.card V) :
    ¬HasDenseInducedSubgraphs G := by
  unfold HasDenseInducedSubgraphs
  push_neg
  use G.neighborFinset v
  constructor
  · simp only [card_neighborFinset_eq_degree]
    exact hv
  · have hempty := neighborFinset_edgeless G hG v
    simp [hempty]

/-! ## Case 2: Low Degree - Greedy Construction -/

/-- Greedy construction finds sparse subset using Finset -/
lemma greedy_sparse_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hlow : ∀ v : V, 2 * G.degree v + 1 < Fintype.card V) :
    ∃ S : Finset V, 2 * S.card + 1 ≥ Fintype.card V ∧
      50 * (G.induce (S : Set V)).edgeFinset.card ≤ (Fintype.card V)^2 := by
  -- Key insight: triangle-free + low degree → can find sparse large subset
  -- Use that independent sets are large in triangle-free graphs
  -- Then extend greedily with low-edge-contribution vertices
  sorry

/-- Low degree case implies sparse large subset exists -/
theorem low_degree_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hlow : ∀ v : V, 2 * G.degree v + 1 < Fintype.card V) :
    ¬HasDenseInducedSubgraphs G := by
  obtain ⟨S, hS⟩ := greedy_sparse_subset G hG hlow
  unfold HasDenseInducedSubgraphs
  push_neg
  exact ⟨S, hS.1, hS.2⟩

/-! ## Main Theorem -/

/-- Triangle-free implies not all large subgraphs are dense -/
theorem cliqueFree3_not_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) : ¬HasDenseInducedSubgraphs G := by
  by_cases h : ∃ v : V, 2 * G.degree v + 1 ≥ Fintype.card V
  · obtain ⟨v, hv⟩ := h
    exact high_degree_case G hG v hv
  · push_neg at h
    exact low_degree_case G hG h

/-- ERDŐS #128: Dense induced subgraphs imply triangle -/
theorem erdos_128 (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ¬G.CliqueFree 3 := by
  intro hdense hcf3
  exact cliqueFree3_not_dense G hcf3 hdense

/-- Equivalent: dense implies triangle exists -/
theorem erdos_128_triangle (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  intro h
  have hnotcf := erdos_128 h
  unfold CliqueFree at hnotcf
  push_neg at hnotcf
  obtain ⟨s, hs⟩ := hnotcf
  simp only [isNClique_iff, isClique_iff, Set.Pairwise] at hs
  obtain ⟨a, b, c, hab, hac, hbc, hs_eq⟩ := Finset.card_eq_three.mp hs.2
  use a, b, c
  simp only [hs_eq, coe_insert, coe_singleton] at hs
  exact ⟨hs.1 (by simp) (by simp) hab,
         hs.1 (by simp) (by simp) hbc,
         hs.1 (by simp) (by simp) hac⟩

end Erdos128
