/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bc3b4df3-dd23-4d6d-ba86-456050c377a7
-/

/-
  slot223e_simple.lean

  LEMMA: A vertex cover of the link graph gives edge cover for triangles
         in the restricted domain.

  SIMPLIFIED VERSION with one sorry for Aristotle.
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangles through v with both other vertices in a given set S -/
def trianglesThroughVinS (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : Finset (Finset V) :=
  G.cliqueFinset 3 |>.filter (fun T => v ∈ T ∧ ∀ x ∈ T, x = v ∨ x ∈ S)

/-- Edges from v to vertices in C -/
def spokesFromV (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : Finset V) : Finset (Sym2 V) :=
  C.biUnion (fun c => if G.Adj v c then {s(v, c)} else ∅)

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
/-- A vertex cover of the link graph gives edge cover for triangles.

    KEY IDEA:
    - C covers all edges (u,w) in S where {v,u,w} is a triangle
    - So for any triangle {v,u,w} with u,w ∈ S, either u ∈ C or w ∈ C
    - Edge {v,u} or {v,w} covers the triangle -/
theorem vertex_cover_to_edge_cover_restricted (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (C : Finset V)
    (hC_subset : C ⊆ S)
    (hC_cover : ∀ u w, u ∈ S → w ∈ S → u ≠ w → G.Adj u w → G.Adj v u → G.Adj v w →
                       u ∈ C ∨ w ∈ C) :
    ∀ T ∈ trianglesThroughVinS G v S, ∃ e ∈ spokesFromV G v C, e ∈ T.sym2 := by
  -- Let T = {v, u, w} be a triangle in trianglesThroughVinS
  -- Then u, w ∈ S and {v,u,w} is a triangle
  -- By hC_cover, u ∈ C or w ∈ C
  -- If u ∈ C: edge s(v,u) ∈ spokesFromV and s(v,u) ∈ T.sym2
  -- If w ∈ C: edge s(v,w) ∈ spokesFromV and s(v,w) ∈ T.sym2
  sorry

/-- The number of covering edges is at most |C| -/
lemma spokes_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (C : Finset V) :
    (spokesFromV G v C).card ≤ C.card := by
  unfold spokesFromV
  apply card_biUnion_le

end