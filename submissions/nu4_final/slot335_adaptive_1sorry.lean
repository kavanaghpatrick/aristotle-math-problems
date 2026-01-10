/-
  slot335: ADAPTIVE 8-edge cover for PATH_4 - SINGLE SORRY VERSION

  KEY INSIGHT (validated by Grok + Gemini):
  The ν=4 constraint restricts which edge types can have externals.
  For each X ∈ M, externals S_X use at most 2 of X's 3 edges.
  Therefore, 2 edges per X (chosen adaptively) suffice → 8 edges total.

  This is the BEST approach per Grok's analysis:
  - slot332 (spine+spoke): too rigid, stuck at 33%
  - slot333 (fixed edges): exposed edge problem, stuck at 22%
  - slot334/335 (adaptive): leverages ν≤4 directly, most promising

  PROOF STRUCTURE:
  1. triangle_classification: Every triangle is M-element, external, or bridge
  2. externals_populate_at_most_two_edges: ν≤4 implies S_X uses ≤2 edge types
  3. two_edges_suffice_per_X: Consequence of (2)
  4. bridges_are_also_externals: Every bridge is external to some X
  5. tau_le_8: Combine (3) and (4) for the main result
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
  (t ∩ S).card ≥ 2

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from previous Aristotle runs)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma sharesEdgeWith_symm (t S : Finset V) : sharesEdgeWith t S ↔ sharesEdgeWith S t := by
  simp only [sharesEdgeWith, Finset.inter_comm]

lemma packing_inter_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y) :
    (X ∩ Y).card ≤ 1 := hM.2 hX hY hXY

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, hm_inter⟩

-- Triangle classification: every triangle is M-element, external, or bridge
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

-- Bridge is also external to its first sharing element
lemma bridge_is_external_to_first (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T X : Finset V)
    (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M)
    (hX : X ∈ M) (hshare : sharesEdgeWith T X) :
    ∃ Y ∈ M, isExternalOf G M Y T ∨ isBridgeTriangle G M T := by
  by_cases h : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
  · exact ⟨X, hX, Or.inl ⟨hT_tri, hT_notin, hshare, h⟩⟩
  · push_neg at h
    obtain ⟨Y, hY, hYne, hYshare⟩ := h
    exact ⟨X, hX, Or.inr ⟨hT_tri, hT_notin, X, Y, hX, hY, hYne.symm, hshare, hYshare⟩⟩

-- Every non-M triangle shares edge with some X, so is covered if X's edges are covered
lemma every_non_M_covered_by_some_X (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := nonpacking_shares_edge G M hM T hT hT_notin

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM (single sorry)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8_path4:

STEP 1: For each X ∈ M, externals S_X populate at most 2 of X's 3 edges.
  PROOF: If S_X has triangles T1, T2, T3 on all 3 edges {a,b}, {a,c}, {b,c} of X = {a,b,c}:
  - T1 = {a, b, x1}, T2 = {a, c, x2}, T3 = {b, c, x3}
  - {T1, T2, T3} is a packing: |Ti ∩ Tj| = 1 for i ≠ j (they share exactly 1 vertex of X)
  - Each Ti is external to X, so |Ti ∩ Y| ≤ 1 for all Y ∈ M \ {X}
  - So {T1, T2, T3} ∪ (M \ {X}) is a packing of size 3 + 3 = 6
  - This contradicts ν ≤ 4!

STEP 2: Therefore, for each X, we can choose 2 edges of X that cover all S_X triangles.
  (Simply pick one edge from each populated edge type.)

STEP 3: For bridges (triangles sharing edges with 2+ M-elements):
  Every bridge shares edge with some X, so it contains 2 vertices of X.
  If our 2 edges for X cover all triangles sharing edge with X, bridges are covered too.

STEP 4: But wait - we chose edges to cover EXTERNALS (S_X), not all T_X triangles.
  Key insight: A bridge B sharing edge with X and Y is NOT in S_X (it also shares with Y).
  However, B IS in T_X (triangles sharing edge with X).

  The fix: Show that the 2 edges chosen for X actually cover ALL T_X, not just S_X.
  This works because:
  - Every triangle in T_X shares 2 vertices with X (so contains one of X's 3 edges)
  - The ν≤4 argument applies to T_X, not just S_X: if T_X uses all 3 edges, we get ν ≥ 5
  - Wait, no - bridges DON'T contribute to the packing contradiction...

STEP 5 (refined): The adaptive approach works because:
  - For externals: 2 edges per X suffice (by ν≤4 argument)
  - For bridges: Every bridge B contains a shared vertex v ∈ X ∩ Y.
    In PATH_4, shared vertices form the "spine": v_ab, v_bc, v_cd.
    Every bridge contains a spine vertex.
    If we include ONE spine edge in our selection for B or C (the middle elements),
    all bridges are covered.

  Specifically for PATH_4:
  - A is endpoint: 2 edges cover S_A and A itself
  - B is middle: choose 2 edges including one spine edge (hitting v_ab or v_bc)
  - C is middle: choose 2 edges including one spine edge (hitting v_bc or v_cd)
  - D is endpoint: 2 edges cover S_D and D itself
  - Bridges X_AB contain v_ab (hit by B's spine edge)
  - Bridges X_BC contain v_bc (hit by B's or C's spine edge)
  - Bridges X_CD contain v_cd (hit by C's spine edge)

CONCLUSION: There exists an 8-edge cover. □
-/

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (h_tri : ∀ X ∈ M, X.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
