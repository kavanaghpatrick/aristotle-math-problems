/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1277ee2d-c8dd-41b7-a2e3-da88d626d1cb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot450_tau_le_8_two_phase.lean

  MAIN THEOREM: τ ≤ 8 for PATH_4 on Fin 9

  Strategy (from multi-agent debate Round 3):
  1. Phase 1: 2 edges per element for S_e coverage → 8 edges max
  2. Phase 2: Bridge external edges if needed (but not needed on Fin 9!)

  On Fin 9, the packing covers all vertices, so no S_e externals exist.
  This means we only need spines (one edge per element) → 4 edges!

  But this doesn't generalize. The full proof needs the 5-packing argument.

  TIER: 1-2 (Fin 9 decidable, generalizable structure)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset

namespace TauLe8TwoPhase

abbrev V9 := Fin 9

-- ══════════════════════════════════════════════════════════════════════════════
-- GRAPH DEFINITION: Complete enough for PATH_4 + bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PATH_4 on vertices 0-8:
  A = {0, 1, 2}
  B = {1, 3, 4}
  C = {4, 5, 6}
  D = {5, 7, 8}

We need edges for:
- All triangles A, B, C, D
- Potential bridges (triangles sharing edge with two adjacent elements)
-/

def PATH4_adj : V9 → V9 → Prop := fun i j =>
  -- Triangle A = {0, 1, 2}
  ({i, j} : Finset V9) ⊆ {0, 1, 2} ∧ i ≠ j ∨
  -- Triangle B = {1, 3, 4}
  ({i, j} : Finset V9) ⊆ {1, 3, 4} ∧ i ≠ j ∨
  -- Triangle C = {4, 5, 6}
  ({i, j} : Finset V9) ⊆ {4, 5, 6} ∧ i ≠ j ∨
  -- Triangle D = {5, 7, 8}
  ({i, j} : Finset V9) ⊆ {5, 7, 8} ∧ i ≠ j

instance : DecidableRel PATH4_adj := fun i j => by
  unfold PATH4_adj
  infer_instance

def G : SimpleGraph V9 where
  Adj := fun i j => PATH4_adj i j ∧ i ≠ j
  symm := by
    intro i j ⟨h, hne⟩
    constructor
    · unfold PATH4_adj at h ⊢
      rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      all_goals (left; constructor) <;> try (right; left; constructor) <;>
        try (right; right; left; constructor) <;> try (right; right; right; constructor)
      all_goals try assumption
      all_goals try exact hne.symm
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> exact h1 (by simp [mem_insert, mem_singleton])
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> exact h1 (by simp [mem_insert, mem_singleton])
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> exact h1 (by simp [mem_insert, mem_singleton])
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> exact h1 (by simp [mem_insert, mem_singleton])
  loopless := by
    intro x ⟨_, hne⟩
    exact hne rfl

instance : DecidableRel G.Adj := fun i j => by
  unfold G
  infer_instance

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 ELEMENTS
-- ══════════════════════════════════════════════════════════════════════════════

def A_elem : Finset V9 := {0, 1, 2}

def B_elem : Finset V9 := {1, 3, 4}

def C_elem : Finset V9 := {4, 5, 6}

def D_elem : Finset V9 := {5, 7, 8}

def M_packing : Finset (Finset V9) := {A_elem, B_elem, C_elem, D_elem}

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC VERIFICATIONS
-- ══════════════════════════════════════════════════════════════════════════════

-- All elements are triangles in G
theorem A_is_triangle : A_elem ∈ G.cliqueFinset 3 := by native_decide

theorem B_is_triangle : B_elem ∈ G.cliqueFinset 3 := by native_decide

theorem C_is_triangle : C_elem ∈ G.cliqueFinset 3 := by native_decide

theorem D_is_triangle : D_elem ∈ G.cliqueFinset 3 := by native_decide

-- PATH_4 intersection structure
theorem AB_inter_card : (A_elem ∩ B_elem).card = 1 := by native_decide

theorem BC_inter_card : (B_elem ∩ C_elem).card = 1 := by native_decide

theorem CD_inter_card : (C_elem ∩ D_elem).card = 1 := by native_decide

-- Non-adjacent disjoint
theorem AC_inter_card : (A_elem ∩ C_elem).card = 0 := by native_decide

theorem AD_inter_card : (A_elem ∩ D_elem).card = 0 := by native_decide

theorem BD_inter_card : (B_elem ∩ D_elem).card = 0 := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- ALL TRIANGLES IN G
-- ══════════════════════════════════════════════════════════════════════════════

-- On this minimal graph, the only triangles are A, B, C, D
theorem all_triangles_are_packing :
    G.cliqueFinset 3 = M_packing := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Since all triangles are in M_packing, we just need to cover A, B, C, D
2. Each triangle needs ONE edge from its 3 edges
3. Total: 4 edges

But to match the 2-per-element strategy:
- A: spine {0,1} or {1,2}
- B: left spine {1,3} or right spine {3,4}
- C: left spine {4,5} or right spine {5,6}
- D: spine {5,7} or {7,8}
-/

-- Cover using one edge per triangle (spines)
def minimal_cover : Finset (Sym2 V9) :=
  {s(0, 1), s(3, 4), s(4, 5), s(7, 8)}

theorem minimal_cover_card : minimal_cover.card = 4 := by native_decide

theorem minimal_cover_in_edges : minimal_cover ⊆ G.edgeFinset := by native_decide

-- Each triangle is covered
theorem A_covered : ∃ e ∈ minimal_cover, e ∈ A_elem.sym2 := by
  use s(0, 1)
  constructor
  · native_decide
  · native_decide

theorem B_covered : ∃ e ∈ minimal_cover, e ∈ B_elem.sym2 := by
  use s(3, 4)
  constructor
  · native_decide
  · native_decide

theorem C_covered : ∃ e ∈ minimal_cover, e ∈ C_elem.sym2 := by
  use s(4, 5)
  constructor
  · native_decide
  · native_decide

theorem D_covered : ∃ e ∈ minimal_cover, e ∈ D_elem.sym2 := by
  use s(7, 8)
  constructor
  · native_decide
  · native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 (actually τ = 4 on this graph!)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8 :
    ∃ Cover : Finset (Sym2 V9),
      Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  use minimal_cover
  refine ⟨?_, ?_, ?_⟩
  -- Cover.card ≤ 8
  · calc minimal_cover.card = 4 := minimal_cover_card
         _ ≤ 8 := by norm_num
  -- Cover ⊆ G.edgeFinset
  · exact minimal_cover_in_edges
  -- All triangles covered
  · intro T hT
    rw [all_triangles_are_packing] at hT
    simp only [M_packing, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact A_covered
    · exact B_covered
    · exact C_covered
    · exact D_covered

-- Actually τ = 4 on this minimal graph
theorem tau_eq_4 :
    ∃ Cover : Finset (Sym2 V9),
      Cover.card = 4 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  use minimal_cover
  refine ⟨minimal_cover_card, minimal_cover_in_edges, ?_⟩
  intro T hT
  rw [all_triangles_are_packing] at hT
  simp only [M_packing, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact A_covered
  · exact B_covered
  · exact C_covered
  · exact D_covered

-- ══════════════════════════════════════════════════════════════════════════════
-- GENERALIZATION NOTE
-- ══════════════════════════════════════════════════════════════════════════════

/-
This graph has no external triangles (no S_e instances) because:
1. All 9 vertices are in the packing
2. Any additional triangle would need vertices from the packing
3. Such triangles would share edges with MULTIPLE packing elements

For graphs WITH external triangles:
- Use the 2-per-element strategy (8 edges total)
- The 5-packing argument shows at most one S_e external per middle
- Bridges don't need extra edges (covered by adaptive choices)

See slot449 for the 5-packing contradiction proof.
-/

end TauLe8TwoPhase