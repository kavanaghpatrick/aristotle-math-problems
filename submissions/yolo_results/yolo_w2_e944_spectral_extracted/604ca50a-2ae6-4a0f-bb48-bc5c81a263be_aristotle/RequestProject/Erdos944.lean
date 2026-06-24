import Mathlib

/-!
# Erdős Problem 944 — k = 4 case

## Problem Statement

Does there exist a finite simple graph G with χ(G) = 4 such that every vertex
is critical (removing any vertex strictly drops χ) yet no single edge is
critical (no single-edge deletion drops χ)?

## Status

**OPEN.** For k ≥ 5, positive constructions exist (Gallai 1963, Stiebitz 1987,
and others). The k = 4 case remains open as of 2026. Neither existence nor
non-existence has been established.

## Mathematical Context

A graph is *k-vertex-critical* if χ(G) = k and χ(G − v) < k for every vertex v.
A graph is *k-(edge-)critical* if χ(G) = k and χ(G − e) < k for every edge e.
Every k-critical graph (in the strong sense) is k-vertex-critical, but the
converse fails in general. The question is whether it can fail specifically at
k = 4 in the strongest way: ALL vertices critical, NO edge critical.

Key obstacles to constructing such a graph:
- K₄ is 4-critical (every edge is critical). ✗
- The Grötzsch graph is 4-critical (every edge is critical). ✗
- Wheels W₅ are 4-vertex-critical but have critical edges. ✗
- Mycielskians are k-critical in the strong sense. ✗
- Hajós constructions produce edge-critical graphs by design. ✗

The spectral approach (Hoffman bound + Nikiforov critical-edge eigenvalue drop)
produces constraints on candidate graphs but does not close the gap.

## Definitions

We define `IsCritical` and `IsCriticalEdge` following the canonical predicates
from FormalConjecturesForMathlib.
-/

open scoped Classical

namespace SimpleGraph

/-- A graph `G` is `k`-vertex-critical if `χ(G) = k` and removing any single
    vertex strictly decreases the chromatic number. -/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
  ∀ v : V, (G.induce ({v}ᶜ : Set V)).chromaticNumber < k

/-- An edge `e` of `G` is critical if it belongs to `G` and deleting it
    strictly decreases the chromatic number. -/
def IsCriticalEdge {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ (G.deleteEdges {e}).chromaticNumber < G.chromaticNumber

end SimpleGraph

/-- **Erdős Problem 944, k = 4 case (OPEN).**

There exists a finite simple graph with chromatic number 4 that is
vertex-critical yet has no critical edge.

**Status:** This is an open problem in combinatorics. The `sorry` below
reflects the unresolved status of this conjecture. Both the existence and
non-existence directions were attempted without success, consistent with the
problem's open status in the literature. -/
theorem yolo_w2_e944_spectral :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.IsCritical 4 ∧
      (∀ e : Sym2 V, ¬ G.IsCriticalEdge e) := by
  sorry
