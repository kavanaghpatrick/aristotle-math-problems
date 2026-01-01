/-
Tuza ν=4: external_tradeoff - Externals trade off with M-elements

GOAL: Prove that if external t has positive weight, some M-element on its
      shared edge must have weight < 1.

This establishes the key trade-off property for LP optimality.

SCAFFOLDING:
- external_shares_M_edge (slot158): every external shares an M-edge

1 SORRY: Apply edge constraint to get the trade-off.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M)

-- SCAFFOLDING: Proven in slot155
axiom M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) : m1 = m2

-- SCAFFOLDING: Proven in slot158
axiom external_shares_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ externals G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2

/-- If external t has positive weight, some M-element sharing an edge has w(m) < 1.

PROOF STRATEGY:
1. t shares M-edge e with some m ∈ M (by external_shares_M_edge)
2. Edge constraint at e: Σ_{s : e ∈ s} w(s) ≤ 1
3. The sum includes at least w(m) + w(t)
4. If w(t) > 0, then w(m) + w(t) ≤ 1 implies w(m) < 1
-/
theorem external_tradeoff (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w)
    (t : Finset V) (ht : t ∈ externals G M) (h_pos : w t > 0) :
    ∃ m ∈ M, ∃ e ∈ M_edges G M, e ∈ t.sym2 ∧ e ∈ m.sym2 ∧ w m < 1 := by
  -- Get the shared M-edge
  obtain ⟨e, he_M, he_t⟩ := external_shares_M_edge G M hM t ht
  -- e ∈ M_edges means ∃ m ∈ M with e ∈ m's edges
  simp only [M_edges, mem_biUnion, mem_filter] at he_M
  obtain ⟨m, hm, he_m, he_G⟩ := he_M
  use m, hm, e
  refine ⟨?_, he_t, he_m, ?_⟩
  · simp only [M_edges, mem_biUnion, mem_filter]
    exact ⟨m, hm, he_m, he_G⟩
  · -- Edge constraint at e: w(m) + w(t) + ... ≤ 1
    -- Since w(t) > 0, w(m) < 1
    sorry
