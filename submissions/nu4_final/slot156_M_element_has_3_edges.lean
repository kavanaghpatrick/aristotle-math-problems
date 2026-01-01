/-
Tuza ν=4: M_element_has_3_edges - Each M-element (3-clique) has exactly 3 edges

GOAL: Prove (m.sym2.filter (· ∈ G.edgeFinset)).card = 3 for m ∈ M.

APPROACH:
- m ∈ cliqueFinset 3 means m.card = 3 and m is a clique
- sym2 of 3-element set {a,b,c} = {{a,b},{a,c},{b,c},{a,a},{b,b},{c,c}}
- Filter to non-diagonals that are edges: exactly {{a,b},{a,c},{b,c}}
- All pairs in a clique are adjacent, so filter keeps all 3

1 SORRY: Prove the combinatorial fact about sym2 and clique edges.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Each M-element (triangle) has exactly 3 edges in G. -/
theorem M_element_has_3_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (m : Finset V) (hm : m ∈ M) :
    (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3 := by
  have hclique : m ∈ G.cliqueFinset 3 := hM.1 hm
  -- m.card = 3 and all distinct pairs are adjacent
  -- sym2 has C(3+1,2) = 6 elements, but 3 are diagonals
  -- The 3 non-diagonal pairs are all edges (clique property)
  -- Key APIs: Finset.card_sym2, SimpleGraph.mem_cliqueFinset_iff
  sorry
