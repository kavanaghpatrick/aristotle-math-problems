/-
Erdős Problem #128 - Triangle in Dense Induced Subgraph
$250 Prize

PROBLEM: Let G be a graph with n vertices such that every induced subgraph
on ≥ ⌊n/2⌋ vertices has more than n²/50 edges. Must G contain a triangle?

CORRECTED FORMALIZATION:
- Previous submission used: 2 * |S| ≥ n (ceil semantics, WRONG)
- This version uses: 2 * |S| + 1 ≥ n (floor semantics, CORRECT)

For n=5:
- Wrong: |S| ≥ 3 (C₅ is counterexample)
- Correct: |S| ≥ 2 (C₅ is NOT counterexample, since {0,2} has 0 edges)

This matches the official FormalConjectures formulation.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Erdos128

open SimpleGraph Set

/-- Every induced subgraph on at least ⌊n/2⌋ vertices has more than n²/50 edges.
    Using: 2 * |S| + 1 ≥ n, which gives |S| ≥ ⌊n/2⌋ -/
def HasDenseInducedSubgraphs (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V →
    50 * (G.induce S).edgeFinset.card > (Fintype.card V)^2

/--
Erdős Problem #128 (OPEN, $250):
If every large induced subgraph is dense (>n²/50 edges),
then G must contain a triangle.

Note: C₅ is NOT a counterexample to this corrected version because:
- For n=5, we need |S| ≥ 2
- The pair {0,2} in C₅ is non-adjacent, so has 0 edges
- 50 * 0 = 0, which is NOT > 25
- So C₅ fails the density condition
-/
theorem erdos_128 (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ¬ G.CliqueFree 3 := by
  sorry

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

/-- C₅ does NOT satisfy the corrected density condition.
    This verifies our formalization is correct. -/
theorem C5_not_dense :
    let C5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b => b = a + 1 ∨ a = b + 1)
    ¬ HasDenseInducedSubgraphs C5 := by
  intro C5
  unfold HasDenseInducedSubgraphs
  push_neg
  -- The set {0, 2} has 2 elements, and 2*2 + 1 = 5 ≥ 5, so it should be checked
  -- But {0, 2} are non-adjacent in C₅, so 0 edges
  use ({0, 2} : Set (Fin 5))
  constructor
  · -- 2 * 2 + 1 = 5 ≥ 5
    simp [Set.ncard]
    decide
  · -- 50 * 0 = 0 ≤ 25
    simp [SimpleGraph.fromRel]
    decide

end Erdos128
