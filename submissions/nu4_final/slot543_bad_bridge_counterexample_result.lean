/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7d77f17c-991a-4d5b-9412-830db53c7fdd

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 177, column 0:
  unexpected end of input; expected 'lemma'
-/

-- GLOBAL ERRORS: These errors are not associated with any specific declaration.
/-
ERROR 1:
unexpected end of input; expected 'lemma'
-/
/-
  slot543: COUNTEREXAMPLE to bridge_has_apex_in_bridge (slot542)

  CLAIM (slot542): For bridge B sharing edges with X,Y ∈ M (ν=4 packing),
  and any apex function (apex Z ∈ Z for all Z ∈ M):
    apex X ∈ B ∨ apex Y ∈ B

  COUNTEREXAMPLE: Graph on Fin 11 with exactly 5 triangles:
    X = {0,1,2}, Y = {2,3,4}, B = {0,2,3}, Z = {5,6,7}, W = {8,9,10}
    M = {X, Y, Z, W} is a maximum 4-packing (ν = 4)
    B is a bridge: shares edge {0,2} with X and edge {2,3} with Y
    apex X = 1, apex Y = 4 — both NOT in B = {0,2,3}
    So apex X ∈ B ∨ apex Y ∈ B is FALSE

  WHY NO 5-PACKING EXISTS:
    B conflicts with X (share {0,2}) and Y (share {2,3}).
    Z and W are isolated cliques on disjoint vertices {5,6,7} and {8,9,10}.
    No other triangles exist in the graph — there are no edges connecting
    the isolated cliques to {0,1,2,3,4}, so no replacement triangles
    can be formed to avoid B's conflicts.

  This falsifies the core lemma of the apex-based τ ≤ 8 approach.
-/

import Mathlib

set_option maxHeartbeats 1600000

open Finset

abbrev V11 := Fin 11

-- The graph: edges of exactly {X, Y, B, Z, W}
-- X = {0,1,2}: edges 0-1, 0-2, 1-2
-- Y = {2,3,4}: edges 2-3, 2-4, 3-4
-- B = {0,2,3}: edges 0-2, 0-3, 2-3
-- Z = {5,6,7}: edges 5-6, 5-7, 6-7
-- W = {8,9,10}: edges 8-9, 8-10, 9-10

def cexAdj : V11 → V11 → Prop :=
  fun a b =>
    -- X = {0,1,2}
    ({a, b} = ({0, 1} : Finset V11)) ∨
    ({a, b} = ({0, 2} : Finset V11)) ∨
    ({a, b} = ({1, 2} : Finset V11)) ∨
    -- Y = {2,3,4}
    ({a, b} = ({2, 3} : Finset V11)) ∨
    ({a, b} = ({2, 4} : Finset V11)) ∨
    ({a, b} = ({3, 4} : Finset V11)) ∨
    -- B = {0,2,3} adds edge 0-3 (0-2 and 2-3 already above)
    ({a, b} = ({0, 3} : Finset V11)) ∨
    -- Z = {5,6,7}
    ({a, b} = ({5, 6} : Finset V11)) ∨
    ({a, b} = ({5, 7} : Finset V11)) ∨
    ({a, b} = ({6, 7} : Finset V11)) ∨
    -- W = {8,9,10}
    ({a, b} = ({8, 9} : Finset V11)) ∨
    ({a, b} = ({8, 10} : Finset V11)) ∨
    ({a, b} = ({9, 10} : Finset V11))

instance : DecidableRel cexAdj := by
  intro a b; unfold cexAdj; infer_instance

-- The adjacency is symmetric (since {a,b} = {b,a} for Finset)
lemma cexAdj_symm : Symmetric cexAdj := by
  intro a b h
  unfold cexAdj at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (simp only [Finset.pair_comm] at h ⊢; tauto)

-- The adjacency is irreflexive
lemma cexAdj_irrefl : ∀ v : V11, ¬ cexAdj v v := by
  intro v h
  unfold cexAdj at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  · simp [Finset.pair_eq_pair_iff] at h

def CexGraph : SimpleGraph V11 where
  Adj := cexAdj
  symm := cexAdj_symm
  loopless := cexAdj_irrefl

instance : DecidableRel CexGraph.Adj := inferInstanceAs (DecidableRel cexAdj)

-- The five triangles as Finset (Fin 11)
def tri_X : Finset V11 := {0, 1, 2}
def tri_Y : Finset V11 := {2, 3, 4}
def tri_B : Finset V11 := {0, 2, 3}
def tri_Z : Finset V11 := {5, 6, 7}
def tri_W : Finset V11 := {8, 9, 10}

-- All five are cliques in CexGraph
lemma tri_X_clique : tri_X ∈ CexGraph.cliqueFinset 3 := by native_decide
lemma tri_Y_clique : tri_Y ∈ CexGraph.cliqueFinset 3 := by native_decide
lemma tri_B_clique : tri_B ∈ CexGraph.cliqueFinset 3 := by native_decide
lemma tri_Z_clique : tri_Z ∈ CexGraph.cliqueFinset 3 := by native_decide
lemma tri_W_clique : tri_W ∈ CexGraph.cliqueFinset 3 := by native_decide

-- The packing M = {X, Y, Z, W}
def M_pack : Finset (Finset V11) := {tri_X, tri_Y, tri_Z, tri_W}

-- M is a triangle packing (all are cliques, pairwise share ≤ 1 vertex)
def isTrianglePacking' (G : SimpleGraph V11) [DecidableRel G.Adj]
    (M : Finset (Finset V11)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  ∀ t1 ∈ M, ∀ t2 ∈ M, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1

instance : DecidablePred (isTrianglePacking' CexGraph) := by
  intro M; unfold isTrianglePacking'; infer_instance

lemma M_is_packing : isTrianglePacking' CexGraph M_pack := by native_decide

-- M is a MAXIMUM packing: every triangle in G shares ≥ 2 vertices with some M-element
-- (i.e., B is the only non-M triangle, and B shares edge with X and Y)
def isMaxPacking' (G : SimpleGraph V11) [DecidableRel G.Adj]
    (M : Finset (Finset V11)) : Prop :=
  isTrianglePacking' G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, 2 ≤ (t ∩ m).card

instance : DecidablePred (isMaxPacking' CexGraph) := by
  intro M; unfold isMaxPacking'; infer_instance

lemma M_is_max_packing : isMaxPacking' CexGraph M_pack := by native_decide

-- ν = 4: no packing of size 5 exists
lemma nu_eq_4 : ∀ P : Finset (Finset V11),
    isTrianglePacking' CexGraph P → P.card ≤ 4 := by native_decide

-- B is a bridge triangle: in G but not in M, shares edges with X and Y
def sharesEdgeWith' (t S : Finset V11) : Prop :=
  2 ≤ (t ∩ S).card

instance : DecidableRel sharesEdgeWith' := by
  intro t S; unfold sharesEdgeWith'; infer_instance

lemma B_is_bridge_triangle :
    tri_B ∈ CexGraph.cliqueFinset 3 ∧
    tri_B ∉ M_pack ∧
    sharesEdgeWith' tri_B tri_X ∧
    sharesEdgeWith' tri_B tri_Y := by native_decide

-- The apex function: apex X = 1, apex Y = 4
-- (Both are vertices of their respective triangles)
lemma apex_X_in_X : (1 : V11) ∈ tri_X := by native_decide
lemma apex_Y_in_Y : (4 : V11) ∈ tri_Y := by native_decide

-- THE FALSIFICATION: both apexes are NOT in B
lemma apex_X_not_in_B : (1 : V11) ∉ tri_B := by native_decide
lemma apex_Y_not_in_B : (4 : V11) ∉ tri_B := by native_decide

-- Therefore the conclusion of slot542's theorem is FALSE for this instance
theorem slot542_conclusion_false :
    ¬ ((1 : V11) ∈ tri_B ∨ (4 : V11) ∈ tri_B) := by
  push_neg
  exact ⟨apex_X_not_in_B, apex_Y_not_in_B⟩

/--
SUMMARY: This is a valid counterexample to slot542's bridge_has_apex_in_bridge.

All hypotheses of slot542 are satisfied:
  ✓ CexGraph is a SimpleGraph on Fin 11
  ✓ M_pack = {X, Y, Z, W} is a maximum 4-packing (isMaxPacking')
  ✓ ν = 4 (no 5-packing exists)
  ✓ tri_B is a bridge triangle (clique in G, not in M, shares edges with X and Y)
  ✓ apex X = 1 ∈ X, apex Y = 4 ∈ Y (valid apex function)

But the conclusion FAILS:
  ✗ apex X = 1 ∉ B = {0,2,3}
  ✗ apex Y = 4 ∉ B = {0,2,3}
  ✗ apex X ∈ B ∨ apex Y ∈ B is FALSE

This means the apex-based approach to τ ≤ 8 (slots 538-542) is fundamentally flawed.
The lemma "if both apexes are outside B, we can build a 5-packing" is FALSE
because the replacement triangles T1, T2 need edges that don't exist in the graph.
-/
