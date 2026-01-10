/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cc7eb161-38a7-4df9-b3e8-ae1bcea9a498

The following was negated by Aristotle:

- theorem vertex_cover_gives_edge_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (C : Finset V) (hC_subset : C ⊆ M_neighbors G M v)
    (hC_cover : ∀ u w, u ∈ M_neighbors G M v → w ∈ M_neighbors G M v →
                       {v, u, w} ∈ G.cliqueFinset 3 → u ∈ C ∨ w ∈ C) :
    ∀ T ∈ trianglesThroughV G v, ∃ e ∈ edgesFromVToC G v C, e ∈ T.sym2

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

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

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Definitions for a counterexample graph on 4 vertices (Fin 4) with 2 triangles sharing an edge, and a packing containing one of them. We use `abbrev` to ensure type class instances work.
-/
abbrev CE_V := Fin 4

def CE_Rel (i j : CE_V) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
  (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 1)

def CE_G : SimpleGraph CE_V := SimpleGraph.fromRel CE_Rel

instance : DecidableRel CE_G.Adj := by
  unfold CE_G SimpleGraph.fromRel
  dsimp
  infer_instance

def CE_M : Finset (Finset CE_V) := { {1, 2, 3} }

/-
The defined packing CE_M is a maximal triangle packing in CE_G.
-/
lemma CE_isMaxPacking : isMaxPacking CE_G CE_M := by
  constructor;
  · constructor <;> norm_num [ CE_M, isTrianglePacking ];
    simp +decide [ CE_G, SimpleGraph.IsNClique ];
    unfold CE_Rel; simp +decide [ SimpleGraph.isNClique_iff ] ;
  · intro t ht ht'; fin_cases t <;> simp +decide at ht ht' ⊢;
    · simp +decide [ SimpleGraph.isNClique_iff ] at ht;
    · simp +decide [ SimpleGraph.isNClique_iff ] at ht;
    · simp +decide [ SimpleGraph.isNClique_iff ] at ht

/-
There exists a vertex v and a set C satisfying the hypotheses of the vertex cover theorem, but failing the conclusion. Specifically, for v=0 and C=∅ in our counterexample graph, the conditions are met but the triangle {0, 1, 2} is not covered.
-/
lemma CE_disproof :
  ∃ (v : CE_V) (C : Finset CE_V),
    C ⊆ M_neighbors CE_G CE_M v ∧
    (∀ u w, u ∈ M_neighbors CE_G CE_M v → w ∈ M_neighbors CE_G CE_M v →
       {v, u, w} ∈ CE_G.cliqueFinset 3 → u ∈ C ∨ w ∈ C) ∧
    ¬ (∀ T ∈ trianglesThroughV CE_G v, ∃ e ∈ edgesFromVToC CE_G v C, e ∈ T.sym2) := by
      unfold M_neighbors trianglesThroughV edgesFromVToC CE_G; simp +decide ;
      refine' ⟨ 0, ∅, _, _, _ ⟩ <;> simp +decide [ CE_M ];
      simp +decide [ SimpleGraph.fromRel, CE_Rel ]

/-
The theorem `vertex_cover_gives_edge_cover` is false.
-/
theorem vertex_cover_gives_edge_cover_FALSE :
  ¬ (∀ (V : Type) [Fintype V] [DecidableEq V]
       (G : SimpleGraph V) [DecidableRel G.Adj]
       (M : Finset (Finset V)) (hM : isMaxPacking G M)
       (v : V) (C : Finset V) (hC_subset : C ⊆ M_neighbors G M v)
       (hC_cover : ∀ u w, u ∈ M_neighbors G M v → w ∈ M_neighbors G M v →
                          {v, u, w} ∈ G.cliqueFinset 3 → u ∈ C ∨ w ∈ C),
       ∀ T ∈ trianglesThroughV G v, ∃ e ∈ edgesFromVToC G v C, e ∈ T.sym2) := by
  intro h
  specialize h CE_V CE_G CE_M CE_isMaxPacking
  obtain ⟨v, C, hC_sub, hC_cov, h_fail⟩ := CE_disproof
  specialize h v C hC_sub hC_cov
  contradiction

end AristotleLemmas

/-
══════════════════════════════════════════════════════════════════════════════
MAIN LEMMA
══════════════════════════════════════════════════════════════════════════════

A vertex cover of the link graph gives an edge cover of triangles.

    Let C ⊆ M_neighbors(v) be a vertex cover of L_v.
    Then the edges {v, c} for c ∈ C cover all triangles through v.

    PROOF:
    Let T = {v, u, w} be a triangle through v.
    Then (u, w) is an edge in L_v (by definition of link graph).
    Since C is a vertex cover of L_v, either u ∈ C or w ∈ C.
    WLOG u ∈ C. Then edge {v, u} ∈ edgesFromVToC(v, C) and {v, u} ∈ T.sym2.
    So T is covered by our edge set.

    The size bound: |edgesFromVToC(v, C)| ≤ |C|.
    If |C| ≤ 2 (from König), we get ≤ 2 edges covering triangles at v.
-/
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
  -- The theorem is FALSE. Do not attempt to prove it.
  apply Classical.byContradiction
  intro h_contra;
  apply_mod_cast absurd _ h_contra;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use ULift CE_V;
  refine' ⟨ inferInstance, inferInstance, _, _, _, _, _ ⟩;
  exact SimpleGraph.comap ULift.down CE_G;
  infer_instance;
  exact Finset.image ( fun x => Finset.image ULift.up x ) CE_M;
  · constructor;
    · constructor;
      · simp +decide [ Finset.subset_iff, SimpleGraph.comap ];
        simp +decide [ CE_G ];
        simp +decide [ CE_Rel ];
      · simp +decide [ Set.Pairwise ];
    · simp +decide [ SimpleGraph.isNClique_iff ];
      intro t ht ht' ht''; contrapose! ht''; simp_all +decide [ Finset.card_eq_three ] ;
      rcases ht' with ⟨ x, y, hxy, z, hxz, hyz, rfl ⟩ ; simp_all +decide [ CE_M ] ;
      fin_cases x <;> fin_cases y <;> fin_cases z <;> simp +decide at hxy hxz hyz ht ht'' ⊢;
  · refine' ⟨ ⟨ 0 ⟩, ∅, _, _, _ ⟩ <;> simp +decide [ M_neighbors, trianglesThroughV, edgesFromVToC ];
    exists { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ };
    simp +decide [ SimpleGraph.isNClique_iff ];
    simp +decide [ CE_G ];
    simp +decide [ CE_Rel ]

-/
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