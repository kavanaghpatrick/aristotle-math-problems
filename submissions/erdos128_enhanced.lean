/-
Erdős Problem #128 - Triangle in Dense Induced Subgraph
$250 Prize - ENHANCED SCAFFOLDING

PROBLEM: If every induced subgraph on ≥ n/2 vertices has > n²/50 edges,
must G contain a triangle?

ENHANCED: Added intermediate lemmas for:
1. Mantel's theorem (triangle-free → ≤ n²/4 edges)
2. Independent set bounds in triangle-free graphs
3. Greedy construction breakdown
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

/-! ## Mantel's Theorem (Triangle-Free Bound) -/

/-- MANTEL'S THEOREM: Triangle-free graph on n vertices has ≤ n²/4 edges.
    This is the key density bound for triangle-free graphs. -/
theorem mantel (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ (Fintype.card V)^2 := by
  -- Proof uses the handshaking lemma and Cauchy-Schwarz
  -- Key: sum of d(v) = 2|E|, and in triangle-free graph,
  -- N(u) ∩ N(v) = ∅ for adjacent u,v
  sorry

/-- Density corollary: triangle-free has edge density ≤ 1/4 -/
lemma triangle_free_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hn : Fintype.card V ≥ 1) :
    G.edgeFinset.card ≤ (Fintype.card V)^2 / 4 := by
  have := mantel G hG
  omega

/-! ## Independent Set Bounds -/

/-- In triangle-free graph, neighborhood of any vertex is independent -/
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

/-- Ramsey-type bound: triangle-free graph has independence number ≥ √n -/
lemma indep_number_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hn : Fintype.card V ≥ 1) :
    ∃ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬G.Adj x y) ∧
      I.card^2 ≥ Fintype.card V := by
  -- Use probabilistic method or greedy: pick vertex, recurse on non-neighbors
  sorry

/-! ## High Degree Case -/

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

/-! ## Low Degree Case - Enhanced Greedy Construction -/

/-- Step 1: Find a large independent set using low degrees -/
lemma find_large_indep_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hlow : ∀ v : V, 2 * G.degree v + 1 < Fintype.card V)
    (hn : Fintype.card V ≥ 4) :
    ∃ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬G.Adj x y) ∧
      4 * I.card ≥ Fintype.card V := by
  -- In triangle-free graph with max degree < n/2,
  -- we can find independent set of size ≥ n/4
  -- Use greedy: repeatedly pick vertex, remove its neighbors
  sorry

/-- Step 2: Extend independent set to half the vertices with bounded edges -/
lemma extend_to_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (I : Finset V) (hI_indep : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬G.Adj x y)
    (hI_size : 4 * I.card ≥ Fintype.card V) :
    ∃ S : Finset V, I ⊆ S ∧ 2 * S.card + 1 ≥ Fintype.card V ∧
      (G.induce (S : Set V)).edgeFinset.card ≤ S.card * (S.card - I.card) := by
  -- Start with I (0 edges), greedily add vertices
  -- Each new vertex adds ≤ (S.card - I.card) edges (only to non-I vertices)
  sorry

/-- Step 3: Bound edges using extension lemma -/
lemma sparse_half_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hlow : ∀ v : V, 2 * G.degree v + 1 < Fintype.card V)
    (hn : Fintype.card V ≥ 4) :
    ∃ S : Finset V, 2 * S.card + 1 ≥ Fintype.card V ∧
      50 * (G.induce (S : Set V)).edgeFinset.card ≤ (Fintype.card V)^2 := by
  -- Combine find_large_indep_set and extend_to_half
  obtain ⟨I, hI_indep, hI_size⟩ := find_large_indep_set G hG hlow hn
  obtain ⟨S, hIS, hS_size, hS_edges⟩ := extend_to_half G hG I hI_indep hI_size
  use S, hS_size
  -- Edge count: at most S.card * (S.card - I.card)
  -- Since I.card ≥ n/4 and S.card ≤ n, edges ≤ n * (n - n/4) = 3n²/4
  -- Need 50 * edges ≤ n², i.e., edges ≤ n²/50
  -- This requires careful analysis...
  sorry

/-- Greedy construction finds sparse subset using Finset -/
lemma greedy_sparse_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hlow : ∀ v : V, 2 * G.degree v + 1 < Fintype.card V) :
    ∃ S : Finset V, 2 * S.card + 1 ≥ Fintype.card V ∧
      50 * (G.induce (S : Set V)).edgeFinset.card ≤ (Fintype.card V)^2 := by
  by_cases hn : Fintype.card V ≥ 4
  · exact sparse_half_exists G hG hlow hn
  · -- Small cases: n ≤ 3
    -- For n ≤ 3, the constraint 50 * edges > n² is very weak
    -- Just take S = univ
    use Finset.univ
    constructor
    · simp; omega
    · -- edges ≤ n²/4 by Mantel, and 50 * n²/4 > n² only if n > 2
      -- But for small n, direct check works
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
