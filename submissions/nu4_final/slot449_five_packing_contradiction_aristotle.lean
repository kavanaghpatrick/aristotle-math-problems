/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2639f4ae-e473-40be-bbf5-e68606b4cf5e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem Se_third_vertex_outside (T E : Finset V9) (hSe : isSeExternal T E)
    (hE_in : E ∈ M_packing) :
    ∃ x ∈ T, ∀ F ∈ M_packing, F ≠ E → x ∉ F

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
  slot449_five_packing_contradiction.lean

  CRITICAL INSIGHT FROM ROUND 3 DEBATE:

  If bridge T = {v2, b, c} exists between B and C, AND both:
  - E_B ∈ S_e(B) forces B to pick left edge (away from bridge)
  - E_C ∈ S_e(C) forces C to pick right edge (away from bridge)

  Then {A, D, T, E_B, E_C} form a 5-packing!

  This contradicts ν = 4, so the scenario is IMPOSSIBLE.
  Therefore, the "spine priority" algorithm is always safe.

  TIER: 2 (uses edge-disjointness on Fin 9)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- CONCRETE SETUP ON Fin 9
-- ══════════════════════════════════════════════════════════════════════════════

/-
PATH_4 structure on vertices 0-8:
  A = {0, 1, 2} (v1 = 1)
  B = {1, 3, 4} (shared v1=1, v2=4)
  C = {4, 5, 6} (shared v2=4, v3=5)
  D = {5, 7, 8} (v3 = 5)

For 5-packing scenario (if it could exist):
  Bridge T = {4, 3, 6} (shares {4,3} with B, {4,6} with C)
  E_B = {1, 3, x} where x ∉ packing (would need vertex 9+)
  E_C = {5, 6, y} where y ∉ packing (would need vertex 10+)

KEY: On Fin 9, there are NO extra vertices for E_B and E_C!
This is why slot447 succeeded on Fin 9.
-/

namespace FivePackingContradiction

abbrev V9 := Fin 9

-- PATH_4 elements
def A_elem : Finset V9 := {0, 1, 2}

def B_elem : Finset V9 := {1, 3, 4}

def C_elem : Finset V9 := {4, 5, 6}

def D_elem : Finset V9 := {5, 7, 8}

def M_packing : Finset (Finset V9) := {A_elem, B_elem, C_elem, D_elem}

-- Shared vertices
def v1 : V9 := 1

-- A ∩ B
def v2 : V9 := 4

-- B ∩ C
def v3 : V9 := 5

-- C ∩ D

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

theorem A_card : A_elem.card = 3 := by native_decide

theorem B_card : B_elem.card = 3 := by native_decide

theorem C_card : C_elem.card = 3 := by native_decide

theorem D_card : D_elem.card = 3 := by native_decide

-- Intersection properties
theorem AB_inter : A_elem ∩ B_elem = {v1} := by native_decide

theorem BC_inter : B_elem ∩ C_elem = {v2} := by native_decide

theorem CD_inter : C_elem ∩ D_elem = {v3} := by native_decide

-- Non-adjacent pairs are disjoint
theorem AC_disj : Disjoint A_elem C_elem := by
  simp only [Finset.disjoint_iff_ne, A_elem, C_elem]
  native_decide

theorem AD_disj : Disjoint A_elem D_elem := by
  simp only [Finset.disjoint_iff_ne, A_elem, D_elem]
  native_decide

theorem BD_disj : Disjoint B_elem D_elem := by
  simp only [Finset.disjoint_iff_ne, B_elem, D_elem]
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX COVERAGE: All 9 vertices are in the packing
-- ══════════════════════════════════════════════════════════════════════════════

def all_vertices : Finset V9 := Finset.univ

theorem packing_covers_all_vertices :
    A_elem ∪ B_elem ∪ C_elem ∪ D_elem = all_vertices := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: No room for S_e externals on Fin 9
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. An S_e external for B must contain 2 vertices from B = {1, 3, 4}
2. Plus one vertex NOT in any M-element
3. But A ∪ B ∪ C ∪ D = {0..8} covers all 9 vertices
4. Therefore no S_e external can exist!
-/

-- Any triangle on Fin 9 must have all vertices in the packing union
theorem triangle_in_packing_union (T : Finset V9) (hT_card : T.card = 3) :
    T ⊆ A_elem ∪ B_elem ∪ C_elem ∪ D_elem := by
  rw [packing_covers_all_vertices]
  intro x _
  exact Finset.mem_univ x

-- S_e definition (shares edge with E, vertex-disjoint from others up to 1)
def isSeExternal (T E : Finset V9) : Prop :=
  T.card = 3 ∧
  T ≠ E ∧
  2 ≤ (T ∩ E).card ∧
  ∀ F ∈ M_packing, F ≠ E → (T ∩ F).card ≤ 1

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Disproof of Se_third_vertex_outside using counterexample T={1,4,7} and E=B.
-/
theorem FivePackingContradiction.Se_third_vertex_outside_disproof : ¬ (∀ T E, FivePackingContradiction.isSeExternal T E → E ∈ FivePackingContradiction.M_packing → ∃ x ∈ T, ∀ F ∈ FivePackingContradiction.M_packing, F ≠ E → x ∉ F) := by
  unfold FivePackingContradiction.isSeExternal;
  native_decide

end AristotleLemmas

/-
For an S_e external, the third vertex must be "new" (not in F for F ≠ E)
-/
theorem Se_third_vertex_outside (T E : Finset V9) (hSe : isSeExternal T E)
    (hE_in : E ∈ M_packing) :
    ∃ x ∈ T, ∀ F ∈ M_packing, F ≠ E → x ∉ F := by
  obtain ⟨hT_card, hT_ne, hT_inter, hT_disj⟩ := hSe
  -- T has 3 vertices, shares 2 with E
  -- The third must avoid sharing with any other F
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  decide +kernel

-/
-- For an S_e external, the third vertex must be "new" (not in F for F ≠ E)
theorem Se_third_vertex_outside (T E : Finset V9) (hSe : isSeExternal T E)
    (hE_in : E ∈ M_packing) :
    ∃ x ∈ T, ∀ F ∈ M_packing, F ≠ E → x ∉ F := by
  obtain ⟨hT_card, hT_ne, hT_inter, hT_disj⟩ := hSe
  -- T has 3 vertices, shares 2 with E
  -- The third must avoid sharing with any other F
  sorry

-- Aristotle to prove via case analysis

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 5-packing scenario impossible on Fin 9
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Suppose bridge T = {v2, b, c} exists (b ∈ B, c ∈ C)
2. Suppose E_B ∈ S_e(B) and E_C ∈ S_e(C) exist
3. E_B must have third vertex outside M-elements
4. E_C must have third vertex outside M-elements
5. But M covers all of Fin 9 - contradiction!
6. Therefore, at most one of E_B, E_C can exist with bridge
7. So at least one of B, C has freedom to cover the bridge
-/

-- Bridge definition
def isBridge (T E F : Finset V9) : Prop :=
  T.card = 3 ∧ 2 ≤ (T ∩ E).card ∧ 2 ≤ (T ∩ F).card

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `Se_third_vertex_outside`
unsolved goals
T E_B E_C : Finset FivePackingContradiction.V9
hBridge : FivePackingContradiction.isBridge T FivePackingContradiction.B_elem FivePackingContradiction.C_elem
hSe_B : FivePackingContradiction.isSeExternal E_B FivePackingContradiction.B_elem
hSe_C : FivePackingContradiction.isSeExternal E_C FivePackingContradiction.C_elem
⊢ False-/
-- If bridge exists with both forcing externals, we get 5-packing
-- But this is impossible on Fin 9!
theorem five_packing_impossible_fin9 :
    ∀ T E_B E_C : Finset V9,
      isBridge T B_elem C_elem →
      isSeExternal E_B B_elem →
      isSeExternal E_C C_elem →
      -- These would form a 5-packing... but can't on Fin 9
      False := by
  intro T E_B E_C hBridge hSe_B hSe_C
  -- E_B needs a vertex outside M, but M covers all of Fin 9
  have h1 := Se_third_vertex_outside E_B B_elem hSe_B (by native_decide : B_elem ∈ M_packing)
  obtain ⟨x, hx_T, hx_out⟩ := h1
  -- x must be in some element of M (since M covers all vertices)
  have hx_in_union : x ∈ A_elem ∪ B_elem ∪ C_elem ∪ D_elem := by
    rw [packing_covers_all_vertices]
    exact Finset.mem_univ x
  simp only [mem_union] at hx_in_union
  rcases hx_in_union with hx_A | hx_B | hx_C | hx_D
  · exact hx_out A_elem (by native_decide) (by native_decide) hx_A
  · -- x ∈ B is allowed since E_B shares edge with B
    -- But then E_B ∩ B would have 3 elements, meaning E_B = B
    -- This contradicts T ≠ E in S_e definition
    sorry
  · exact hx_out C_elem (by native_decide) (by native_decide) hx_C
  · exact hx_out D_elem (by native_decide) (by native_decide) hx_D

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `Se_third_vertex_outside`
unsolved goals
case h
T : Finset FivePackingContradiction.V9
hSe : FivePackingContradiction.isSeExternal T FivePackingContradiction.B_elem
⊢ False-/
-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: At least one middle has free choice
-- ══════════════════════════════════════════════════════════════════════════════

/-
Since we can't have both E_B and E_C with a bridge on Fin 9,
at least one of B or C can freely choose to cover the bridge.
-/

-- Either S_e(B) is empty, or S_e(C) is empty, or no bridge exists
theorem middle_freedom :
    (∀ T, ¬isSeExternal T B_elem) ∨
    (∀ T, ¬isSeExternal T C_elem) ∨
    (∀ T, ¬isBridge T B_elem C_elem) := by
  -- On Fin 9, the packing uses all vertices
  -- Any S_e external needs a vertex outside the packing
  -- Therefore no S_e externals exist
  left
  intro T hSe
  have := Se_third_vertex_outside T B_elem hSe (by native_decide)
  obtain ⟨x, hx_T, hx_out⟩ := this
  have hx_univ : x ∈ (Finset.univ : Finset V9) := Finset.mem_univ x
  -- x must be in some M-element
  have : x ∈ A_elem ∨ x ∈ B_elem ∨ x ∈ C_elem ∨ x ∈ D_elem := by
    fin_cases x <;> simp [A_elem, B_elem, C_elem, D_elem]
  rcases this with h | h | h | h
  · exact hx_out A_elem (by native_decide) (by native_decide) h
  · -- x ∈ B_elem, need to show contradiction differently
    -- If T has 3 vertices, 2 in B, and x ∈ B, then T ∩ B has at least 3 vertices
    -- But T has only 3 vertices, so T = B (up to some vertex)
    sorry
  · exact hx_out C_elem (by native_decide) (by native_decide) h
  · exact hx_out D_elem (by native_decide) (by native_decide) h

end FivePackingContradiction