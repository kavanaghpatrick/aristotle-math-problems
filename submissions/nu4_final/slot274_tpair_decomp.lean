/-
slot274: PATH_4 τ ≤ 8 via T_pair Decomposition (Gemini recommended)

STRATEGY: Decompose into two "bowtie" subproblems.
- T_pair(A,B) = triangles sharing edge with A OR B
- T_pair(C,D) = triangles sharing edge with C OR D
- By maximality: All triangles ∈ T_pair(A,B) ∪ T_pair(C,D)
- Prove: τ(T_pair(A,B)) ≤ 4 (bowtie with shared vertex v1)
- Prove: τ(T_pair(C,D)) ≤ 4 (bowtie with shared vertex v3)
- By subadditivity: τ ≤ 4 + 4 = 8

KEY INSIGHT: A bowtie (two triangles sharing exactly one vertex) has τ ≤ 4.
The 4-edge cover for bowtie at v: pick 2 edges incident to v from each triangle.
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

/-- T_pair(e,f) = triangles sharing edge with e OR f -/
def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2)

/-
PROOF SKETCH:
1. Every triangle shares edge with some M-element (maximality)
2. M = {A, B, C, D}, so every triangle shares edge with A, B, C, or D
3. If shares with A or B: t ∈ T_pair(A,B)
4. If shares with C or D: t ∈ T_pair(C,D)
5. Hence G.cliqueFinset 3 ⊆ T_pair(A,B) ∪ T_pair(C,D)

For τ(T_pair(A,B)) ≤ 4:
- A and B share exactly vertex v1
- 4-edge cover: {v1,a1}, {v1,a2} from A, {v1,v2}, {v1,b'} from B
- Every triangle in T_pair(A,B) contains v1 OR shares base {a1,a2} or {v2,b'}
- If contains v1: covered by star edges
- If shares {a1,a2}: covered by... hmm, {a1,a2} not in cover!

ISSUE: Bowtie cover works for triangles CONTAINING the shared vertex,
but not for triangles sharing the BASE edges opposite the shared vertex.

REVISED APPROACH: Use 2 edges per original M-triangle, selected to cover bases.
For A: use {v1,a1} and {a1,a2} (covers leg and base)
For B: use {v1,b'} and {v2,b'} (covers both legs from b')
Total from A∪B: 4 edges

Hmm, but {v1,a2,x} is missed if we use {v1,a1} and {a1,a2}!

Let Aristotle figure out the right selection.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  sorry

end
