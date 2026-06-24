import Mathlib

open scoped Classical

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 944 — Dirac's Conjecture, k = 4 case

## Background

Dirac (1970) asked: for every k ≥ 4, does there exist a graph G with chromatic
number k such that every vertex is critical (removing any vertex drops χ) yet
no edge is critical (every edge is "redundant" — its removal does not drop χ)?

## Known results

- **k = 5**: Solved by Brown (1992), who constructed a 5-vertex-critical graph
  with no critical edge.
- **k − 1 not prime**: Solved by Lattanzio (2002).
- **k ≥ 5**: Solved by Jensen (2002), giving constructions for all k ≥ 5.
- **k = 4**: **OPEN.** Brown's k = 5 example does not descend; Jensen's family
  starts at k = 5; Lattanzio's condition fails since 4 − 1 = 3 is prime.

## Status

This is the last remaining case of Dirac's 1970 conjecture. Either:
- A 4-vertex-critical graph with no critical edge exists (resolving the
  conjecture positively for k = 4), or
- Every 4-vertex-critical graph has a critical edge (resolving it negatively
  for k = 4).

Neither direction has been established.
-/

/-- A graph `G` is **k-vertex-critical** if its chromatic number is exactly `k`
and for every vertex `v`, the induced subgraph on `V \ {v}` has chromatic number
strictly less than `k`. -/
def SimpleGraph.IsVertexCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧
  ∀ v : V, (G.induce ({v}ᶜ : Set V)).chromaticNumber < (k : ℕ∞)

/-- An edge `e` of `G` is **critical** if removing it strictly drops the
chromatic number. -/
def SimpleGraph.IsEdgeCritical {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  (G.deleteEdges {e}).chromaticNumber < G.chromaticNumber

/-- **Dirac's conjecture, k = 4 case (Erdős Problem 944).**

There exists a finite 4-vertex-critical graph in which no single edge is critical
(i.e., removing any one edge does not reduce the chromatic number).

**Status: OPEN.** This is the last remaining case of Dirac's 1970 conjecture.
All cases k ≥ 5 have been resolved positively (Jensen, 2002). -/
theorem erdos_944_k_eq_four :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.IsVertexCritical 4 ∧
      ∀ e : Sym2 V, ¬G.IsEdgeCritical e := by
  sorry
