/-
  slot332: COORDINATED EDGE SELECTION for tau_le_8

  KEY INSIGHT FROM GROK ANALYSIS:
  The 8 "spoke" edges (private-to-shared) DON'T cover bridges!
  Bridges live in the K4 on shared vertices and use "spine" edges.

  CORRECT APPROACH:
  1. Select all 4 SPINE edges (one per M-triangle): covers M-elements + bridges
  2. Select 4 SPOKE edges (one per M-triangle): covers externals

  For PATH_4: A = {v_da, v_ab, a}, B = {v_ab, v_bc, b}, C = {v_bc, v_cd, c}, D = {v_cd, v_da, d}
  - Spine edges: {v_da, v_ab}, {v_ab, v_bc}, {v_bc, v_cd}, {v_cd, v_da}
  - Spoke edges: {v_ab, a}, {v_bc, b}, {v_cd, c}, {v_da, d} (or similar)

  WHY THIS WORKS:
  1. M-elements: Each has exactly one spine edge, which is selected.
  2. Externals: Use apex structure from universal_apex_exists.
     - If apex v ∈ X: spoke edges {v, a}, {v, b} cover externals
     - If apex t ∉ X: spoke edge to t covers externals
  3. Bridges: Every bridge uses at least one spine edge (from the K4 on shared vertices)
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS (Aristotle verified - 0 sorry)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨h u (Sym2.mem_iff.mpr (Or.inl rfl)), h v (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ (∃ X ∈ M, isExternalOf G M X T) ∨ isBridgeTriangle G M T := by
  by_cases hT_in : T ∈ M
  · left; exact hT_in
  · right
    obtain ⟨X, hX_in, hX_share⟩ := nonpacking_shares_edge G M hM T hT hT_in
    by_cases h_unique : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
    · left; exact ⟨X, hX_in, hT, hT_in, hX_share, h_unique⟩
    · right; push_neg at h_unique
      obtain ⟨Y, hY_in, hY_ne, hY_share⟩ := h_unique
      exact ⟨hT, hT_in, X, Y, hX_in, hY_in, hY_ne.symm, hX_share, hY_share⟩

-- Bridge shares edge with SOME M-element (proven by Aristotle)
lemma bridge_covered_by_some_m_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (hT : isBridgeTriangle G M T) :
    ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  obtain ⟨_, _, X, _, hX_in, _, _, hX_share, _⟩ := hT
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hX_share
  exact ⟨X, hX_in, u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge uses SPINE edge (edge between two shared vertices)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH: bridge_uses_spine_edge

A bridge B shares edges with X and Y (distinct M-elements).
- B ∩ X has 2 vertices (by sharesEdgeWith)
- B ∩ Y has 2 vertices (by sharesEdgeWith)
- B has 3 vertices total

CLAIM: B ∩ X ∩ Y is nonempty (has at least 1 vertex).

Proof: If B ∩ X ∩ Y = ∅, then |B| ≥ |B ∩ X| + |B ∩ Y| ≥ 2 + 2 = 4 > 3. Contradiction.

Let v ∈ B ∩ X ∩ Y. Since B ∩ X has 2 vertices, let {v, u} ⊆ B ∩ X.
Since v ∈ Y and u ∈ X, and X ∩ Y has at most 1 vertex (packing constraint),
we have u ∉ Y (otherwise |X ∩ Y| ≥ 2).

So {v, u} is an edge of B where:
- v ∈ X ∩ Y (shared between X and Y)
- u ∈ X \ Y

This edge {v, u} is in X. If we select one edge from each X that hits
the shared vertex with neighbors, bridges are covered.

ALTERNATIVELY: Select all "spine" edges (edges between shared vertices).
Every bridge has at least one such edge.
-/
lemma bridge_inter_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (B X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hBX : sharesEdgeWith B X) (hBY : sharesEdgeWith B Y)
    (hB_card : B.card = 3) :
    (B ∩ X ∩ Y).Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  have hBX_ge : (B ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B X |>.mp hBX
  have hBY_ge : (B ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B Y |>.mp hBY
  have h_disj : Disjoint (B ∩ X) (B ∩ Y) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    convert h_empty using 1
    ext v; simp [Finset.mem_inter]
  have h_union_card : ((B ∩ X) ∪ (B ∩ Y)).card ≥ 4 := by
    rw [Finset.card_union_of_disjoint h_disj]; omega
  have h_sub : (B ∩ X) ∪ (B ∩ Y) ⊆ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv' | hv'
    · exact Finset.mem_of_mem_inter_left hv'
    · exact Finset.mem_of_mem_inter_left hv'
  have := Finset.card_le_card h_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- COORDINATED COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for coordinated_8_cover:

For each X ∈ M, select 2 edges:
  - e_spine: One edge of X between two vertices that are shared with other M-elements
  - e_spoke: One edge of X to the private vertex (for externals)

Total: 4 × 2 = 8 edges

COVERAGE:
1. M-elements: Each X is hit by e_spine (which is an edge of X).

2. Externals: For X-external T:
   - T shares edge with X, so T ∩ X has 2 vertices
   - T doesn't share edge with other M-elements
   - By universal_apex_exists, T contains the apex vertex
   - If apex ∈ X: e_spoke hits T (apex is in both X and T)
   - If apex ∉ X: The apex t is in T, and T's edge with X is {a, b} ⊂ X
     We need to ensure {a, b} or an edge involving t is selected.

3. Bridges: For bridge B:
   - B shares edges with X and Y (at least)
   - By bridge_inter_nonempty, ∃ v ∈ B ∩ X ∩ Y
   - The edge in B ∩ X containing v is either selected as e_spine for X or Y
   - Specifically: If v is the shared vertex of X and Y, then the spine edge
     of X (containing v) is in B.
-/
theorem coordinated_8_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
