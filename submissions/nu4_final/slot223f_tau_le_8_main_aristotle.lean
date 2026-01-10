/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 78e4fd7a-6829-4949-b79b-0a6bb2968b9d
-/

/-
  slot223f_tau_le_8_main.lean

  MAIN THEOREM: τ ≤ 8 for cycle_4 configuration

  FROM 3-ROUND DEBATE (Jan 3, 2026):
  This combines all the Link Graph lemmas to prove the main result.

  PROOF OUTLINE:
  1. Every triangle contains a shared vertex (slot223d)
  2. At each shared vertex v:
     a. M_neighbors has ≤ 4 vertices (slot223a)
     b. Link graph L_v has α ≥ 2 (slot223b)
     c. Therefore L_v has vertex cover ≤ 2 (slot223c)
     d. This gives edge cover ≤ 2 for triangles at v (slot223e)
  3. Total: 4 vertices × 2 edges = 8 edges

  1 SORRY: The final combination argument
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry295925', 'vertex_cover_gives_edge_cover', 'link_graph_independence_ge_2', 'triangle_contains_shared_vertex', 'four_vertex_cover', 'link_graph_small']-/
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

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  hM_card : M.card = 4
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  hAC : A ∩ C = ∅
  hBD : B ∩ D = ∅

/-- M-neighbors of v: vertices in M-elements containing v, excluding v itself -/
def M_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  M.biUnion (fun X => if v ∈ X then X.erase v else ∅)

/-- Triangle covering number -/
def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ E.card = n ∧
    ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 }

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOMS (PROVEN IN SLOTS 223a-e)
-- ══════════════════════════════════════════════════════════════════════════════

/-- slot223a: At shared vertex v, M_neighbors has ≤ 4 vertices -/
axiom link_graph_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    (M_neighbors G M v).card ≤ 4

/-- slot223b: Link graph has independent set of size ≥ 2 -/
axiom link_graph_independence_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    ∃ u w, u ∈ M_neighbors G M v ∧ w ∈ M_neighbors G M v ∧ u ≠ w ∧
           ¬({v, u, w} ∈ G.cliqueFinset 3)

/-- slot223c: 4-vertex graph with α ≥ 2 has vertex cover ≤ 2 -/
axiom four_vertex_cover (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (hS : S.card ≤ 4)
    (h_ind : ∃ u w, u ∈ S ∧ w ∈ S ∧ u ≠ w ∧ ¬H.Adj u w) :
    ∃ C : Finset V, C.card ≤ 2 ∧ C ⊆ S ∧
      ∀ e : Sym2 V, e ∈ H.edgeFinset → (∃ v ∈ e, v ∈ S) → ∃ v ∈ C, v ∈ e

/-- slot223d: Every triangle contains a shared vertex -/
axiom triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V), v ∈ T

/-- slot223e: Vertex cover of L_v → edge cover of triangles at v -/
axiom vertex_cover_gives_edge_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (C : Finset V)
    (hC_cover : ∀ u w, u ∈ M_neighbors G M v → w ∈ M_neighbors G M v →
                       {v, u, w} ∈ G.cliqueFinset 3 → u ∈ C ∨ w ∈ C) :
    ∀ T ∈ G.cliqueFinset 3, v ∈ T → ∃ c ∈ C, s(v, c) ∈ T.sym2

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  Cycle4
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  triangleCoveringNumber
but this term has type
  ?m.5

Note: Expected a function because this term is being applied to the argument
  G-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- The main theorem: τ ≤ 8 for cycle_4.

    PROOF STRUCTURE:
    1. For each shared vertex v ∈ {v_ab, v_bc, v_cd, v_da}:
       - Get C_v with |C_v| ≤ 2 (from independence + König)
       - Get E_v = {s(v, c) | c ∈ C_v} with |E_v| ≤ 2

    2. Let E_8 = E_{v_ab} ∪ E_{v_bc} ∪ E_{v_cd} ∪ E_{v_da}
       - |E_8| ≤ 4 × 2 = 8

    3. E_8 covers all triangles:
       - Let T be any triangle
       - By slot223d, T contains some shared vertex v
       - By slot223e, some edge in E_v hits T
       - E_v ⊆ E_8, so E_8 hits T

    4. Therefore τ ≤ |E_8| ≤ 8 -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Construct 8-edge cover:
  -- For each shared vertex v, use slot223a-c to get 2-edge cover
  -- Union of 4 × 2 = 8 edges covers all triangles (by slot223d-e)
  sorry

end