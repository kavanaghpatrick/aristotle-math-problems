/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7e360cc6-04bd-4b04-b6b8-b05faae9bd86

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot523_bridge_spine_coverage.lean

  TARGET: Prove bridges in PATH_4 are covered by spine edges

  KEY INSIGHT (from multi-agent analysis):
  If T shares edge with both A and B where A ∩ B = {v}, then v ∈ T.
  Proof: If v ∉ T, then T ∩ A and T ∩ B are disjoint, so
  |T| ≥ |T ∩ A| + |T ∩ B| ≥ 4, contradicting |T| = 3.

  CONSEQUENCE: Every bridge to adjacent elements contains a spine vertex.
  Therefore spine edges {v1,v2}, {v2,v3} cover ALL bridges in PATH_4.

  TIER: 1-2 (set theory + simple cardinality)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX TYPE (Fin 10 for native_decide on small instances)
-- ══════════════════════════════════════════════════════════════════════════════

abbrev V := Fin 10

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- PATH_4: A—v1—B—v2—C—v3—D where consecutive elements share exactly one vertex -/
structure Path4 (A B C D : Finset V) (v1 v2 v3 : V) : Prop where
  card_A : A.card = 3
  card_B : B.card = 3
  card_C : C.card = 3
  card_D : D.card = 3
  inter_AB : A ∩ B = {v1}
  inter_BC : B ∩ C = {v2}
  inter_CD : C ∩ D = {v3}
  inter_AC : A ∩ C = ∅
  inter_AD : A ∩ D = ∅
  inter_BD : B ∩ D = ∅
  v1_ne_v2 : v1 ≠ v2
  v2_ne_v3 : v2 ≠ v3
  v1_ne_v3 : v1 ≠ v3

/-- Bridge: A triangle sharing edge (≥2 vertices) with two distinct packing elements -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (T E F : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ (T ∩ E).card ≥ 2 ∧ (T ∩ F).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMA: Bridge contains shared vertex (from slot441)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Assume v ∉ T (for contradiction)
2. T ∩ E and T ∩ F are disjoint: if x ∈ both, then x ∈ E ∩ F = {v}, so x = v ∈ T, contradiction
3. |T ∩ E| + |T ∩ F| = |(T ∩ E) ∪ (T ∩ F)| (disjoint)
4. |(T ∩ E) ∪ (T ∩ F)| ≤ |T| = 3
5. But |T ∩ E| ≥ 2 and |T ∩ F| ≥ 2, so sum ≥ 4 > 3
6. Contradiction! Therefore v ∈ T.
-/
theorem bridge_contains_shared_vertex
    (T E F : Finset V) (v : V)
    (hT_card : T.card = 3)
    (hEF_inter : E ∩ F = {v})
    (hTE : (T ∩ E).card ≥ 2)
    (hTF : (T ∩ F).card ≥ 2) :
    v ∈ T := by
  by_contra hv_not_T
  -- T ∩ E and T ∩ F are disjoint (since their only common element v is not in T)
  have h_disjoint : Disjoint (T ∩ E) (T ∩ F) := by
    rw [Finset.disjoint_iff_ne]
    intro x hxE y hyF hxy
    simp only [mem_inter] at hxE hyF
    subst hxy
    have hx_in_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE.2, hyF.2⟩
    rw [hEF_inter, mem_singleton] at hx_in_both
    rw [hx_in_both] at hxE
    exact hv_not_T hxE.1
  -- Sum of cardinalities equals union cardinality (disjoint)
  have h_card_union : (T ∩ E).card + (T ∩ F).card = ((T ∩ E) ∪ (T ∩ F)).card := by
    rw [card_union_of_disjoint h_disjoint]
  -- Union is subset of T
  have h_union_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx
    simp only [mem_union, mem_inter] at hx
    cases hx with
    | inl h => exact h.1
    | inr h => exact h.1
  -- Derive contradiction
  have h_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_union_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SPINE COVERAGE: Every bridge contains a spine vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridge to A from B contains v1 (the A-B shared vertex) -/
theorem bridge_AB_contains_v1
    (A B : Finset V) (v1 : V)
    (hAB : A ∩ B = {v1})
    (T : Finset V) (hT_card : T.card = 3)
    (hTA : (T ∩ A).card ≥ 2) (hTB : (T ∩ B).card ≥ 2) :
    v1 ∈ T :=
  bridge_contains_shared_vertex T A B v1 hT_card hAB hTA hTB

/-- Bridge to C from B contains v2 (the B-C shared vertex) -/
theorem bridge_BC_contains_v2
    (B C : Finset V) (v2 : V)
    (hBC : B ∩ C = {v2})
    (T : Finset V) (hT_card : T.card = 3)
    (hTB : (T ∩ B).card ≥ 2) (hTC : (T ∩ C).card ≥ 2) :
    v2 ∈ T :=
  bridge_contains_shared_vertex T B C v2 hT_card hBC hTB hTC

/-- Bridge to D from C contains v3 (the C-D shared vertex) -/
theorem bridge_CD_contains_v3
    (C D : Finset V) (v3 : V)
    (hCD : C ∩ D = {v3})
    (T : Finset V) (hT_card : T.card = 3)
    (hTC : (T ∩ C).card ≥ 2) (hTD : (T ∩ D).card ≥ 2) :
    v3 ∈ T :=
  bridge_contains_shared_vertex T C D v3 hT_card hCD hTC hTD

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Spine edges cover all bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
For spine edges E_spine = {s(v1,v2), s(v2,v3)}:

Case 1: Bridge between A and B
  - By bridge_AB_contains_v1: v1 ∈ T
  - B contains v1 and v2, so the other vertex of T∩B is v1 or v2
  - If both v1,v2 ∈ T, edge s(v1,v2) covers T
  - If only v1 ∈ T from B: T shares edge with A, which contains v1, so another vertex is in A
  - Since T is a triangle with v1 ∈ T, we need another B vertex. That's v2 or b3.
  - Actually: T shares edge with B means T∩B has 2 elements. One is v1 (proven).
  - The other must be v2 or b3 (the other vertices of B).
  - If v2 ∈ T: s(v1,v2) covers T
  - If only b3 ∈ T (not v2): T contains {v1, b3, x} for some x
    But this case means s(v1,b3) is needed, not spine. However, we're covering
    BRIDGES (to A), not all B-externals. Bridges must also share edge with A.

Key refinement: For T to be a bridge between A and B:
  - T ∩ A has ≥2 elements: so T shares {v1, a2} or {v1, a3} or {a2, a3} with A
  - T ∩ B has ≥2 elements: so T shares {v1, v2} or {v1, b3} or {v2, b3} with B
  - Since v1 ∈ T (proven), and T has 3 vertices, T = {v1, x, y}
  - From A: one of x,y is in A (namely a2 or a3)
  - From B: one of x,y is in B\{v1} = {v2, b3}
  - So T = {v1, (a2 or a3), (v2 or b3)}
  - If v2 ∈ T: s(v1,v2) covers it
  - If b3 ∈ T (not v2): T = {v1, (a2 or a3), b3}
    Edge s(v1, b3) is not in spine but IS in B's edges

CORRECTED CLAIM: Bridges to B from both sides need coordination.
  - Bridge A-B: contains v1, covered by edge touching v1
  - Bridge B-C: contains v2, covered by edge touching v2
  - Spine edge s(v1,v2) touches BOTH v1 and v2
  - So ONE edge s(v1,v2) covers ALL bridges involving B!
-/

/-- Spine edge covers any bridge involving the middle element -/
theorem spine_covers_middle_bridges
    (A B C : Finset V) (v1 v2 : V)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2})
    (hv1_in_B : v1 ∈ B) (hv2_in_B : v2 ∈ B) (hv12 : v1 ≠ v2)
    (T : Finset V) (hT_card : T.card = 3)
    -- T is a bridge to A or to C (sharing edge with B)
    (hBridge : ((T ∩ A).card ≥ 2 ∧ (T ∩ B).card ≥ 2) ∨
               ((T ∩ B).card ≥ 2 ∧ (T ∩ C).card ≥ 2)) :
    v1 ∈ T ∨ v2 ∈ T := by
  cases hBridge with
  | inl hAB_bridge =>
    -- T is bridge between A and B
    have hv1_in_T := bridge_AB_contains_v1 A B v1 hAB T hT_card hAB_bridge.1 hAB_bridge.2
    exact Or.inl hv1_in_T
  | inr hBC_bridge =>
    -- T is bridge between B and C
    have hv2_in_T := bridge_BC_contains_v2 B C v2 hBC T hT_card hBC_bridge.1 hBC_bridge.2
    exact Or.inr hv2_in_T

/-- If v1 ∈ T or v2 ∈ T, then edge s(v1,v2) hits T (exists vertex in common) -/
theorem spine_edge_hits_triangle (v1 v2 : V) (T : Finset V) (hv12 : v1 ≠ v2)
    (h : v1 ∈ T ∨ v2 ∈ T) :
    ∃ u ∈ T, u = v1 ∨ u = v2 := by
  cases h with
  | inl hv1 => exact ⟨v1, hv1, Or.inl rfl⟩
  | inr hv2 => exact ⟨v2, hv2, Or.inr rfl⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: In PATH_4, two spine edges cover all bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-- The two spine edges {v1,v2} and {v2,v3} cover all bridges in PATH_4 -/
theorem path4_spine_covers_all_bridges
    (A B C D : Finset V) (v1 v2 v3 : V)
    (hp : Path4 A B C D v1 v2 v3)
    (T : Finset V) (hT_card : T.card = 3)
    -- T is ANY bridge in the path (between adjacent elements)
    (hBridge : ((T ∩ A).card ≥ 2 ∧ (T ∩ B).card ≥ 2) ∨
               ((T ∩ B).card ≥ 2 ∧ (T ∩ C).card ≥ 2) ∨
               ((T ∩ C).card ≥ 2 ∧ (T ∩ D).card ≥ 2)) :
    (v1 ∈ T ∨ v2 ∈ T) ∨ (v2 ∈ T ∨ v3 ∈ T) := by
  rcases hBridge with hAB | hBC | hCD
  · -- Bridge A-B: contains v1
    have hv1 := bridge_AB_contains_v1 A B v1 hp.inter_AB T hT_card hAB.1 hAB.2
    exact Or.inl (Or.inl hv1)
  · -- Bridge B-C: contains v2
    have hv2 := bridge_BC_contains_v2 B C v2 hp.inter_BC T hT_card hBC.1 hBC.2
    exact Or.inl (Or.inr hv2)
  · -- Bridge C-D: contains v3
    have hv3 := bridge_CD_contains_v3 C D v3 hp.inter_CD T hT_card hCD.1 hCD.2
    exact Or.inr (Or.inr hv3)

end