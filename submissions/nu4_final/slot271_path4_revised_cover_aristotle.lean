/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2a09e6a7-1ec9-42aa-b013-c8bc2ec68973
-/

/-
slot271: PATH_4 τ ≤ 8 via Star Cover from Spine Vertices

INSIGHT: Previous cover A.sym2 ∪ {v1v2, v2v3} ∪ D.sym2 misses triangles
like {v1, b', x} that share edge with B but not A.

REVISED COVER: Star from v1 and v3 (edges incident to spine endpoints).
- From v1: {v1,a1}, {v1,a2}, {v1,v2}, {v1,b'} = 4 edges
- From v3: {v3,c'}, {v2,v3}, {v3,d1}, {v3,d2} = 4 edges
Total: 8 edges

This covers more triangles but may still miss {a1,a2,x} and {d1,d2,x}.
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

/-- Star cover: edges incident to v1 from A∪B, edges incident to v3 from C∪D -/
def path4_star_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  (cfg.A.sym2 ∪ cfg.B.sym2).filter (fun e => cfg.v1 ∈ e ∧ e ∈ G.edgeFinset) ∪
  (cfg.C.sym2 ∪ cfg.D.sym2).filter (fun e => cfg.v3 ∈ e ∧ e ∈ G.edgeFinset)

/- Aristotle failed to find a proof. -/
/-
PROOF SKETCH for τ ≤ 8:
1. path4_star_cover has ≤ 8 edges (4 from v1 star + 4 from v3 star)
2. Every triangle t shares edge with some e ∈ M by maximality
3. Case analysis shows star edges from v1 and v3 cover all triangles:
   - If v1 ∈ t: edge {v1, x} for some x ∈ t is in v1-star
   - If v3 ∈ t: edge {v3, x} for some x ∈ t is in v3-star
   - If v1, v3 ∉ t: by triangle_structure, (t∩A).card ≥ 2 or (t∩D).card ≥ 2
     * If (t∩A).card ≥ 2 ∧ v1 ∉ t: t ⊇ {a1, a2}. Edge {a1,a2} NOT in star!
       But then t shares edge with A only, not B,C,D.
       Check: can such t exist while satisfying maximality? Need to verify.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  sorry

end