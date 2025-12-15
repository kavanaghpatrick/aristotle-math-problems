/-
Erdős Problem #128 - Triangle in Dense Induced Subgraph
$250 Prize - STRUCTURAL APPROACH

STRATEGY: Prove the contrapositive
  CliqueFree 3 G → ¬HasDenseInducedSubgraphs G

KEY INSIGHT: In a triangle-free graph G:
1. The neighborhood of any vertex is an INDEPENDENT SET (0 edges)
2. If any vertex has degree ≥ n/2, its neighborhood is a large sparse induced subgraph
3. This violates the density condition (needs > n²/50 edges)

MATHEMATICAL ARGUMENT:
- Let G be triangle-free on n vertices
- Pick any vertex v with maximum degree d = Δ(G)
- Case 1: d ≥ ⌊n/2⌋
  - N(v) has |N(v)| = d ≥ ⌊n/2⌋ vertices
  - N(v) is independent (triangle-free), so 0 edges
  - 0 ≤ n²/50, violating density condition ✓
- Case 2: d < ⌊n/2⌋ for all vertices
  - Total edges ≤ nd/2 < n²/4
  - Use probabilistic/averaging argument for sparse large subgraph
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Erdos128

open SimpleGraph Set Finset

/-- Every induced subgraph on at least ⌊n/2⌋ vertices has more than n²/50 edges -/
def HasDenseInducedSubgraphs (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V →
    50 * (G.induce S).edgeFinset.card > (Fintype.card V)^2

/-! ## Key Structural Lemmas for Triangle-Free Graphs -/

/-- In a triangle-free graph, the neighborhood of any vertex is an independent set -/
lemma neighborSet_independent_of_cliqueFree3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    (G.neighborSet v).Pairwise (fun x y => ¬G.Adj x y) := by
  intro x hx y hy hne
  -- If x, y ∈ N(v) and x ~ y, then {v, x, y} forms a triangle
  intro hadj
  apply hG {v, x, y}
  simp only [isNClique_iff, isClique_iff, Set.Pairwise, coe_insert, coe_singleton,
             Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro a ha b hb hab
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals (try exact (hab rfl).elim)
    · exact hx  -- v ~ x
    · exact hy  -- v ~ y
    · exact G.symm hx
    · exact hadj
    · exact G.symm hy
    · exact G.symm hadj
  · simp [card_insert_of_not_mem, card_singleton]
    intro h; exact hne (h.symm)

/-- The induced subgraph on the neighborhood of a vertex in a triangle-free graph has no edges -/
lemma neighborSet_induce_edgeless (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    (G.induce (G.neighborSet v)).edgeFinset = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro e he
  -- Extract the edge
  have := neighborSet_independent_of_cliqueFree3 G hG v
  sorry

/-- If a vertex has degree ≥ ⌊n/2⌋, then its neighborhood violates density condition -/
lemma high_degree_contradicts_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) (hv : 2 * G.degree v + 1 ≥ Fintype.card V) :
    ¬HasDenseInducedSubgraphs G := by
  unfold HasDenseInducedSubgraphs
  push_neg
  use G.neighborSet v
  constructor
  · -- |N(v)| ≥ ⌊n/2⌋
    simp only [Set.ncard_eq_toFinset_card', neighborSet_toFinset, card_neighborFinset_eq_degree]
    exact hv
  · -- Induced subgraph has 0 edges (since neighborhood is independent)
    have hempty := neighborSet_induce_edgeless G hG v
    simp [hempty]

/-- Turán bound: triangle-free graphs have at most n²/4 edges -/
lemma turan_triangle_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ (Fintype.card V)^2 := by
  sorry

/-- In a triangle-free graph with all degrees < n/2, we can find a sparse large subgraph -/
lemma low_degree_sparse_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hlow : ∀ v : V, 2 * G.degree v + 1 < Fintype.card V) :
    ∃ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce S).edgeFinset.card ≤ (Fintype.card V)^2 := by
  sorry

/-! ## Main Theorem via Contrapositive -/

/-- CONTRAPOSITIVE: Triangle-free implies not all large subgraphs are dense -/
theorem cliqueFree3_not_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) : ¬HasDenseInducedSubgraphs G := by
  by_cases h : ∃ v : V, 2 * G.degree v + 1 ≥ Fintype.card V
  · -- Case 1: Some vertex has high degree
    obtain ⟨v, hv⟩ := h
    exact high_degree_contradicts_density G hG v hv
  · -- Case 2: All vertices have low degree
    push_neg at h
    obtain ⟨S, hS⟩ := low_degree_sparse_subgraph G hG h
    unfold HasDenseInducedSubgraphs
    push_neg
    exact ⟨S, hS.1, hS.2⟩

/--
Erdős Problem #128 (OPEN, $250):
If every large induced subgraph is dense (>n²/50 edges),
then G must contain a triangle.
-/
theorem erdos_128 (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ¬ G.CliqueFree 3 := by
  intro hdense hcf3
  exact cliqueFree3_not_dense G hcf3 hdense

/-- Equivalent formulation: dense implies triangle exists -/
theorem erdos_128' (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  intro h
  have := erdos_128 h
  unfold CliqueFree at this
  push_neg at this
  obtain ⟨s, hs⟩ := this
  simp only [isNClique_iff, isClique_iff, Set.Pairwise] at hs
  have hcard := hs.2
  obtain ⟨a, b, c, hab, hac, hbc, hs_eq⟩ := Finset.card_eq_three.mp hcard
  use a, b, c
  simp only [hs_eq, Finset.coe_insert, Finset.coe_singleton] at hs
  exact ⟨hs.1 (by simp) (by simp) hab,
         hs.1 (by simp) (by simp) hbc,
         hs.1 (by simp) (by simp) hac⟩

/-- C₅ does NOT satisfy the density condition -/
theorem C5_not_dense :
    let C5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b => b = a + 1 ∨ a = b + 1)
    ¬ HasDenseInducedSubgraphs C5 := by
  intro C5
  unfold HasDenseInducedSubgraphs
  push_neg
  use ({0, 2} : Set (Fin 5))
  constructor
  · simp [Set.ncard]; decide
  · simp [SimpleGraph.fromRel]; decide

end Erdos128
