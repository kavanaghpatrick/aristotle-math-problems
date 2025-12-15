/-
Erdős Problem #128 - Triangle in Dense Induced Subgraph
$250 Prize - GREEDY CONSTRUCTION APPROACH

PROBLEM: If every induced subgraph on ≥ n/2 vertices has > n²/50 edges,
must G contain a triangle?

STRATEGY: Prove contrapositive - triangle-free → find sparse large subset

CASE 1 (PROVEN): High degree vertex exists (deg ≥ n/2)
- Neighborhood N(v) is independent (0 edges) in triangle-free graph
- Take S = N(v): |S| ≥ n/2 and edges(S) = 0 ≤ n²/50

CASE 2 (GREEDY): All degrees < n/2
- Use greedy construction: iteratively add vertices minimizing edges
- Triangle-free graphs have large independent sets
- Start with independent set (0 edges), extend carefully
-/

import Mathlib

set_option maxHeartbeats 400000

open SimpleGraph Set Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Erdos128

/-- Every induced subgraph on ≥ n/2 vertices has > n²/50 edges -/
def HasDenseInducedSubgraphs (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V →
    50 * (G.induce S).edgeFinset.card > (Fintype.card V)^2

/-! ## Case 1: High Degree Vertex -/

/-- In triangle-free graph, neighborhood is independent -/
lemma neighborSet_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    ∀ x ∈ G.neighborSet v, ∀ y ∈ G.neighborSet v, x ≠ y → ¬G.Adj x y := by
  intro x hx y hy hne hadj
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
lemma neighborSet_edgeless (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    (G.induce (G.neighborSet v)).edgeFinset = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro e he
  cases e
  simp only [mem_edgeFinset, induce_adj] at he
  obtain ⟨⟨hx, hy⟩, hadj⟩ := he
  have hpw := neighborSet_independent G hG v
  exact hpw _ hx _ hy (ne_of_adj hadj) hadj

/-- High degree case: neighborhood is large and sparse -/
theorem high_degree_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) (hv : 2 * G.degree v + 1 ≥ Fintype.card V) :
    ¬HasDenseInducedSubgraphs G := by
  unfold HasDenseInducedSubgraphs
  push_neg
  use G.neighborSet v
  constructor
  · simp only [Set.ncard_eq_toFinset_card', neighborSet_toFinset, card_neighborFinset_eq_degree]
    exact hv
  · have hempty := neighborSet_edgeless G hG v
    simp [hempty]

/-! ## Case 2: Low Degree - Greedy Construction -/

/-- Greedy selection: repeatedly add vertex with minimum neighbors in S -/
-- Key insight: In triangle-free graph, we can find large independent set
-- Then extend with low-connectivity vertices

/-- Triangle-free graphs have independence number ≥ sqrt(n) -/
lemma triangle_free_large_independent_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hn : Fintype.card V ≥ 4) :
    ∃ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬G.Adj x y) ∧
      I.card * I.card ≥ Fintype.card V := by
  -- Use Ramsey-type argument or direct construction
  sorry

/-- Greedy construction finds sparse subset -/
lemma greedy_sparse_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hlow : ∀ v : V, 2 * G.degree v + 1 < Fintype.card V) :
    ∃ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce S).edgeFinset.card ≤ (Fintype.card V)^2 := by
  -- Strategy: Start with large independent set I (from triangle-free property)
  -- Add remaining vertices greedily, minimizing edge contribution
  -- Key: Each added vertex contributes < n/2 edges (by degree bound)
  -- Need to show: total edges ≤ n²/50

  -- Step 1: Get independent set I with |I|² ≥ n
  -- Step 2: If |I| ≥ n/2, done (0 edges)
  -- Step 3: Otherwise, add vertices one by one
  --         Each vertex adds at most deg(v) < n/2 edges to S
  --         Adding k vertices adds at most k * n/2 edges
  --         We need k ≤ n/2 more vertices
  --         Total edges ≤ (n/2) * (n/2) / 2 = n²/8 for greedy part
  --         But we need n²/50, so use better bound...

  -- Alternative: Use averaging over all n/2-subsets
  -- Expected edges = |E| * C(n/2, 2) / C(n, 2) ≈ |E|/4
  -- |E| ≤ n²/4 (Turán) implies expected ≤ n²/16
  -- But n²/16 > n²/50, so averaging alone insufficient

  -- Key improvement: In low-degree case, use vertex ordering
  -- Order vertices by degree, take first n/2
  -- These contribute fewer edges than average
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

/-- Equivalent formulation: dense implies triangle exists -/
theorem erdos_128_triangle (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  intro h
  have := erdos_128 h
  unfold CliqueFree at this
  push_neg at this
  obtain ⟨s, hs⟩ := this
  simp only [isNClique_iff, isClique_iff, Set.Pairwise] at hs
  obtain ⟨a, b, c, hab, hac, hbc, hs_eq⟩ := Finset.card_eq_three.mp hs.2
  use a, b, c
  simp only [hs_eq, coe_insert, coe_singleton] at hs
  exact ⟨hs.1 (by simp) (by simp) hab,
         hs.1 (by simp) (by simp) hbc,
         hs.1 (by simp) (by simp) hac⟩

end Erdos128
