/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ab501d47-a5f9-48b7-9e1b-e34b1ea3574d

The following was proved by Aristotle:

- theorem M_element_has_3_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (m : Finset V) (hm : m ∈ M) :
    (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3
-/

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
  -- Since $m$ is a clique of size 3, every pair of vertices in $m$ is connected by an edge. The number of such pairs is $C(3,2) = 3$.
  have h_edges : ∀ v w : V, v ∈ m → w ∈ m → v ≠ w → G.Adj v w := by
    simp_all +decide [ SimpleGraph.isNClique_iff ];
    exact fun v w hv hw hvw => hclique.1 hv hw hvw;
  -- Since $m$ is a clique of size 3, we can write $m$ as $\{v_1, v_2, v_3\}$ for some vertices $v_1, v_2, v_3$.
  obtain ⟨v1, v2, v3, hv⟩ : ∃ v1 v2 v3 : V, m = {v1, v2, v3} ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 := by
    simp_all +decide [ SimpleGraph.cliqueFinset ];
    rcases Finset.card_eq_three.mp hclique.2 with ⟨ v1, v2, v3, hv1, hv2, hv3 ⟩ ; use v1, v2, v3 ; aesop;
  have h_edges : Finset.filter (fun e => e ∈ G.edgeFinset) (Finset.sym2 m) = {Sym2.mk (v1, v2), Sym2.mk (v1, v3), Sym2.mk (v2, v3)} := by
    ext ⟨ x, y ⟩ ; aesop;
  rw [ h_edges, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> simp +decide [ hv ]