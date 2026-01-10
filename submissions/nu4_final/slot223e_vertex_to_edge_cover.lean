/-
  slot223e_vertex_to_edge_cover.lean

  LEMMA: A vertex cover of L_v gives an edge cover of triangles through v.

  FROM 3-ROUND DEBATE (Jan 3, 2026):
  This bridges the Link Graph approach to the actual triangle covering.

  PROOF IDEA:
  At shared vertex v, let L_v be the link graph on M-neighbors.
  If C is a vertex cover of L_v, then the edges {v, c} for c ∈ C
  cover all triangles through v.

  Why: A triangle {v, u, w} through v corresponds to edge (u, w) in L_v.
  If C covers L_v, then u ∈ C or w ∈ C.
  So edge {v, u} or {v, w} hits the triangle.

  1 SORRY: The vertex cover to edge cover conversion
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

/-- M-neighbors of v: vertices in M-elements containing v, excluding v itself -/
def M_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  M.biUnion (fun X => if v ∈ X then X.erase v else ∅)

/-- Triangles through v: triangles containing vertex v -/
def trianglesThroughV (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  G.cliqueFinset 3 |>.filter (fun T => v ∈ T)

/-- Edges from v to a set C -/
def edgesFromVToC (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (C : Finset V) : Finset (Sym2 V) :=
  C.biUnion (fun c => if G.Adj v c then {s(v, c)} else ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- A vertex cover of the link graph gives an edge cover of triangles.

    Let C ⊆ M_neighbors(v) be a vertex cover of L_v.
    Then the edges {v, c} for c ∈ C cover all triangles through v.

    PROOF:
    Let T = {v, u, w} be a triangle through v.
    Then (u, w) is an edge in L_v (by definition of link graph).
    Since C is a vertex cover of L_v, either u ∈ C or w ∈ C.
    WLOG u ∈ C. Then edge {v, u} ∈ edgesFromVToC(v, C) and {v, u} ∈ T.sym2.
    So T is covered by our edge set.

    The size bound: |edgesFromVToC(v, C)| ≤ |C|.
    If |C| ≤ 2 (from König), we get ≤ 2 edges covering triangles at v. -/
theorem vertex_cover_gives_edge_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (C : Finset V) (hC_subset : C ⊆ M_neighbors G M v)
    (hC_cover : ∀ u w, u ∈ M_neighbors G M v → w ∈ M_neighbors G M v →
                       {v, u, w} ∈ G.cliqueFinset 3 → u ∈ C ∨ w ∈ C) :
    ∀ T ∈ trianglesThroughV G v, ∃ e ∈ edgesFromVToC G v C, e ∈ T.sym2 := by
  -- For any triangle T = {v, u, w} through v:
  -- 1. u, w ∈ M_neighbors(v) (they're the other two vertices)
  -- 2. {v, u, w} is a triangle, so (u, w) is an L_v edge
  -- 3. By hC_cover, u ∈ C or w ∈ C
  -- 4. The corresponding edge {v, u} or {v, w} is in edgesFromVToC
  -- 5. That edge is in T.sym2
  sorry

/-- The edge set has size at most |C| -/
lemma edgesFromVToC_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : Finset V) :
    (edgesFromVToC G v C).card ≤ C.card := by
  -- Each c ∈ C contributes at most 1 edge {v, c}
  -- So |edgesFromVToC| ≤ |C|
  unfold edgesFromVToC
  apply card_biUnion_le

end
