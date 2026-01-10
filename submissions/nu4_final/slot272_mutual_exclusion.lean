/-
slot272: PATH_4 τ ≤ 8 via Mutual Exclusion of Bad Triangles

KEY INSIGHT: The "bad" triangles that require special edges are:
- {a1, a2, x}: shares edge only with A, requires {a1, a2}
- {d1, d2, y}: shares edge only with D, requires {d1, d2}
- {v1, b', z}: shares edge with B, requires {v1, b'}
- {v2, b', w}: shares edge with B, requires {v2, b'}
- Similar for C

HYPOTHESIS: These triangles are mutually exclusive in ways that allow 8 edges.

Specifically, if we pick edges adaptively based on which triangles exist:
- If {a1, a2, x} exists: use {a1, a2} (else use {v1, a1}, {v1, a2})
- If {d1, d2, y} exists: use {d1, d2} (else use {v3, d1}, {v3, d2})

This adaptive selection gives us 8 edges that cover all triangles.

ALTERNATIVE: Prove that in PATH_4 with maximal packing, the graph structure
prevents more than 8 distinct "required" edges.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v1 : V
  v2 : V
  v3 : V
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅

/-- Triangles sharing edge with a specific M-element -/
def trianglesSharingEdgeWith (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

/-
PROOF SKETCH for main theorem:
1. Partition triangles by which M-element they share edge with
2. For A: ≤ 2 edges needed (endpoint)
3. For B: ≤ 2 edges needed (middle, shares v1 with A and v2 with C)
4. For C: ≤ 2 edges needed (middle)
5. For D: ≤ 2 edges needed (endpoint)
6. Total: ≤ 8 edges

The key is that triangles sharing edge with MULTIPLE M-elements are covered
by any of those elements' edge allocations.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  sorry

end
