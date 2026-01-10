/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 05121e94-88bc-4357-b57d-b7075777f166

The following was proved by Aristotle:

- theorem triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V), v ∈ T
-/

/-
  slot223d_triangle_contains_shared.lean

  LEMMA: Every triangle in cycle_4 contains at least one shared vertex.

  FROM 3-ROUND DEBATE (Jan 3, 2026):
  This is essential for the Link Graph approach - it ensures all triangles
  are "seen" by one of the 4 link graphs at shared vertices.

  PROOF IDEA:
  Let T be any triangle in G. By maximality of M, either:
  1. T ∈ M: Then T is A, B, C, or D, which all contain shared vertices
  2. T ∉ M: By maximality, T shares an edge with some M ∈ M.
     - If T ∩ M contains an edge, T shares 2 vertices with M
     - At least one of those is a shared vertex of M

  Actually, the key insight: In cycle_4, the 4 shared vertices {v_ab, v_bc, v_cd, v_da}
  form an "edge cover" of M in the intersection graph sense.

  1 SORRY: The maximality + containment argument
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

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle contains at least one shared vertex.

    In cycle_4, shared vertices = {v_ab, v_bc, v_cd, v_da}.

    PROOF:
    Case 1: T ∈ M. Then T is A, B, C, or D.
    - A contains v_ab and v_da (both shared)
    - B contains v_ab and v_bc (both shared)
    - C contains v_bc and v_cd (both shared)
    - D contains v_cd and v_da (both shared)

    Case 2: T ∉ M. By maximality, T shares an edge with some X ∈ M.
    - T ∩ X contains 2 vertices of X
    - X is a triangle with 3 vertices, 2 of which are shared vertices
    - So at least one vertex in T ∩ X is shared.

    The key observation: Each M-element has 2 shared vertices out of 3.
    Any 2-subset of a 3-set must overlap with a 2-subset. -/
theorem triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V), v ∈ T := by
  -- Let S = {v_ab, v_bc, v_cd, v_da} be the shared vertices
  -- Case 1: T ∈ M
  -- Case 2: T ∉ M, so T shares edge with some X ∈ M, and that edge contains a shared vertex
  --
  -- Key insight: In each M-element X:
  -- - A = {v_ab, v_da, a_priv}: 2 shared, 1 private
  -- - B = {v_ab, v_bc, b_priv}: 2 shared, 1 private
  -- - C = {v_bc, v_cd, c_priv}: 2 shared, 1 private
  -- - D = {v_cd, v_da, d_priv}: 2 shared, 1 private
  --
  -- Any 2 vertices of X include at least 1 shared vertex (by pigeonhole on 2-of-3)
  -- Since T ∩ X has 2 vertices, at least one is shared.
  -- Let's unfold the definition of `Cycle4` to use the properties of the configuration.
  rcases cfg with ⟨A, B, C, D, hA, hB, hC, hD, hM_eq, hM_card, v_ab, v_bc, v_cd, v_da, hAB, hBC, hCD, hDA, hAC, hBD⟩;
  -- By definition of `Cycle4`, each M-element has exactly 2 shared vertices.
  have hM_vertices : ∀ t ∈ M, t.card = 3 ∧ (t ∩ {v_ab, v_bc, v_cd, v_da}).card = 2 := by
    intro t ht
    have ht_card : t.card = 3 := by
      have := hM.1.1 ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.2;
    -- Since $t \in M$, we know that $t$ must be one of $A$, $B$, $C$, or $D$.
    have ht_cases : t = A ∨ t = B ∨ t = C ∨ t = D := by
      aesop;
    rcases ht_cases with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Finset.ext_iff ];
    · grind;
    · grind;
    · grind;
    · grind;
  -- By maximality, T shares an edge e with some X in M. T ∩ e = e.
  by_cases hT_in_M : T ∈ M;
  · specialize hM_vertices T hT_in_M;
    obtain ⟨ v, hv ⟩ := Finset.card_pos.mp ( by linarith : 0 < Finset.card ( T ∩ { v_ab, v_bc, v_cd, v_da } ) ) ; use v; aesop;
  · -- By maximality, T shares an edge with some X in M.
    obtain ⟨X, hX_in_M, hX_edge⟩ : ∃ X ∈ M, (T ∩ X).card ≥ 2 := by
      have := hM.2 T hT hT_in_M; aesop;
    -- Since T ∩ X has at least 2 elements and X has exactly 2 shared vertices, T must contain at least one of these shared vertices.
    have hT_shared_vertex : (T ∩ X ∩ {v_ab, v_bc, v_cd, v_da}).card ≥ 1 := by
      have hT_shared_vertex : (T ∩ X ∩ {v_ab, v_bc, v_cd, v_da}).card = (T ∩ X).card + ({v_ab, v_bc, v_cd, v_da} ∩ X).card - (T ∩ X ∪ {v_ab, v_bc, v_cd, v_da} ∩ X).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
      have hT_shared_vertex : (T ∩ X ∪ {v_ab, v_bc, v_cd, v_da} ∩ X).card ≤ X.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      grind +ring;
    obtain ⟨ v, hv ⟩ := Finset.card_pos.mp hT_shared_vertex; use v; aesop;

end