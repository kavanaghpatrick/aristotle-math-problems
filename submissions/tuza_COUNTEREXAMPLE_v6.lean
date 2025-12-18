/-
TUZA'S CONJECTURE - COUNTEREXAMPLE TO v6 "NEARBY TRIANGLES" APPROACH
====================================================================
Source: Aristotle output cca06048-9d55-432f-97ae-510829f1cf0a
Submission: v6 prescriptive (NearbyTriangles approach)

WHAT ARISTOTLE FOUND:
The lemma `two_edges_cover_nearby` is FALSE.

COUNTEREXAMPLE: K₄ (complete graph on 4 vertices)
- P = {{0,1,2}} is a maximum packing (ν = 1)
- p = {0,1,2} has edges: {0,1}, {1,2}, {0,2}
- Nearby triangles:
  * t₁ = {0,1,3} shares ONLY edge {0,1}
  * t₂ = {1,2,3} shares ONLY edge {1,2}
  * t₃ = {0,2,3} shares ONLY edge {0,2}

WHY 2 EDGES CAN'T COVER ALL NEARBY:
- Any 2 edges from p leave one edge uncovered
- The uncovered edge's nearby triangle is not hit
- Example: {0,1}, {1,2} covers t₁, t₂ but NOT t₃

LESSON: The structural constraints in our proof strategy don't guarantee
that 2 edges suffice for covering nearby triangles.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set of triangles is a packing if they are all triangles in G and are pairwise edge-disjoint. -/
def IsTrianglePacking (P : Finset (Finset V)) : Prop :=
  (∀ t ∈ P, t ∈ G.cliqueFinset 3) ∧
  (P : Set (Finset V)).Pairwise fun t1 t2 ↦ (t1 ∩ t2).card ≤ 1

/-- A packing is maximum if no other packing has a larger cardinality. -/
def IsMaxTrianglePacking (P : Finset (Finset V)) : Prop :=
  IsTrianglePacking G P ∧ ∀ P', IsTrianglePacking G P' → P'.card ≤ P.card

/-- The edges of a triangle `t` (as a set of 3 vertices). -/
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.sym2.filter (fun e ↦ ¬ e.IsDiag)

/-- Two triangles share an edge if they share at least 2 vertices. -/
def shareEdge (t1 t2 : Finset V) : Prop :=
  2 ≤ (t1 ∩ t2).card

/-- A triangle `t` is nearby `p` with respect to packing `P` if it shares an edge with `p`
    and shares no edges with any other triangle in `P`. -/
def is_nearby (P : Finset (Finset V)) (p t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧
  shareEdge p t ∧
  ∀ p' ∈ P, p' ≠ p → ¬ shareEdge p' t

/-! ### PROVEN: Counterexample using K₄ -/

/-- There exists a graph G and a maximum packing P such that two_edges_cover_nearby is FALSE -/
theorem two_edges_cover_nearby_counterexample :
    ∃ (V : Type) (inst : Fintype V) (inst2 : DecidableEq V) (G : SimpleGraph V) (inst3 : DecidableRel G.Adj)
      (P : Finset (Finset V)) (hP : IsMaxTrianglePacking G P) (p : Finset V) (hp : p ∈ P),
    ¬ ∃ e1 e2, e1 ∈ triangleEdges p ∧ e2 ∈ triangleEdges p ∧
    ∀ t, is_nearby G P p t → (e1 ∈ triangleEdges t ∨ e2 ∈ triangleEdges t) := by
  let V := Fin 4
  let G : SimpleGraph V := ⊤
  let p : Finset V := {0, 1, 2}
  let P : Finset (Finset V) := {p}
  have hP : IsMaxTrianglePacking G P := by
    constructor
    · simp [IsTrianglePacking, p, G]; decide
    · intro P' hP'
      -- In K4, any two triangles share an edge.
      -- So a packing can have at most 1 triangle.
      unfold IsTrianglePacking at hP';
      native_decide +revert
  use V, inferInstance, inferInstance, G, inferInstance, P, hP, p, (by simp [P])
  push_neg
  intro e1 e2 he1 he2
  -- We need to find a nearby triangle t not covered by e1, e2.
  -- The nearby triangles are t1={0,1,3}, t2={1,2,3}, t3={0,2,3}.
  -- e1, e2 are edges of p={0,1,2}.
  -- WLOG e1={0,1}, e2={1,2}. Then t3={0,2,3} is not covered.
  obtain ⟨t, ht⟩ : ∃ t : Finset V, t ∈ G.cliqueFinset 3 ∧ shareEdge p t ∧ t ≠ p ∧ e1 ∉ triangleEdges t ∧ e2 ∉ triangleEdges t := by
    revert e1 e2;
    simp +decide [ triangleEdges, shareEdge ];
    native_decide;
  unfold is_nearby; aesop;

end
