import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Erdős Problem 944 — Dirac's Conjecture, k = 4 Case

## Problem

Dirac (1970) asked: for every k ≥ 4, does there exist a finite simple graph G with
chromatic number k such that every vertex is critical (removing any vertex strictly drops χ)
yet no single edge is critical (no single-edge deletion drops χ)?

## Known results

- For k ≥ 5, the answer is **yes**. Constructions are known via Hajós calculus
  modifications and Jensen-type gluing operations.
- For k = 4, the problem is **OPEN** as of 2026.

## Why k = 4 is hard

Every known 4-critical graph has at least one critical edge. The smallest 4-critical graphs
(K₄, odd wheels W₅, W₇, …, the Grötzsch graph) all have critical edges. The gluing
techniques that work for k ≥ 5 rely on the existence of a base template with k ≥ 5
chromatic number, and cannot be bootstrapped down to k = 4.

Gallai (1963) showed that in a k-critical graph, the subgraph induced on minimum-degree
vertices has special structure (disjoint unions of cliques and odd cycles). For k = 4
this severely constrains candidates, making exhaustive construction difficult.

## Definitions

We define `SimpleGraph.IsCritical` and `SimpleGraph.IsCriticalEdge` following the standard
combinatorial definitions.
-/

namespace SimpleGraph

/-- A simple graph `G` is `k`-vertex-critical if its chromatic number equals `k` and
removing any vertex strictly reduces the chromatic number. -/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
  ∀ (v : V), (G.induce ({v}ᶜ : Set V)).chromaticNumber < k

/-- An edge `e` of `G` is critical if deleting it strictly reduces the chromatic number. -/
def IsCriticalEdge {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  (G.deleteEdges {e}).chromaticNumber < G.chromaticNumber

end SimpleGraph

/-!
## The Open Problem Statement

The following asserts the existence of a finite 4-vertex-critical graph with no critical
edges. This is the k = 4 case of Dirac's conjecture (Erdős Problem 944).

**Status: OPEN.** Neither existence nor non-existence has been established.
The `sorry` below reflects this genuinely open status.
-/

/-- Erdős Problem 944 (k = 4): There exists a finite 4-vertex-critical graph
in which no single edge is critical. **OPEN PROBLEM** -/
theorem yolo6_erdos_944_k_eq_four :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.IsCritical 4 ∧
      (∀ e : Sym2 V, ¬ G.IsCriticalEdge e) := by
  sorry
