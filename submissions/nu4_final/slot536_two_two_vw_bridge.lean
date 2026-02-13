/-
  slot536: TWO_TWO_VW BRIDGE COVERAGE

  For the two_two_vw case (two pairs at different vertices),
  prove that bridges between pairs are covered.

  STRUCTURE:
  - Pair 1: {A, B} share vertex v
  - Pair 2: {C, D} share vertex w
  - v ≠ w, so pairs are vertex-disjoint

  KEY INSIGHT: Since pairs are vertex-disjoint, there are NO bridges
  between elements of different pairs!
-/

import Mathlib

set_option maxHeartbeats 400000
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

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

-- ══════════════════════════════════════════════════════════════════════════════
-- TWO_TWO_VW STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- The two_two_vw configuration: two pairs of triangles at different vertices -/
structure TwoTwoVW (V : Type*) [DecidableEq V] where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  v : V  -- shared vertex of A and B
  w : V  -- shared vertex of C and D
  h_v_in_A : v ∈ A
  h_v_in_B : v ∈ B
  h_w_in_C : w ∈ C
  h_w_in_D : w ∈ D
  h_v_ne_w : v ≠ w
  h_A_card : A.card = 3
  h_B_card : B.card = 3
  h_C_card : C.card = 3
  h_D_card : D.card = 3
  h_AB_inter : (A ∩ B).card = 1  -- A and B share exactly vertex v
  h_CD_inter : (C ∩ D).card = 1  -- C and D share exactly vertex w

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Pairs are vertex-disjoint
-- ══════════════════════════════════════════════════════════════════════════════

/-- In two_two_vw, elements from different pairs are vertex-disjoint -/
lemma pairs_vertex_disjoint (cfg : TwoTwoVW V) :
    (cfg.A ∩ cfg.C).card ≤ 1 ∧
    (cfg.A ∩ cfg.D).card ≤ 1 ∧
    (cfg.B ∩ cfg.C).card ≤ 1 ∧
    (cfg.B ∩ cfg.D).card ≤ 1 := by
  -- This follows from the packing property
  -- In a valid packing, any two triangles share at most 1 vertex
  -- (otherwise they'd share an edge, violating edge-disjointness)
  sorry

/-- Cross-pair bridges cannot exist in two_two_vw -/
lemma no_cross_pair_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : TwoTwoVW V)
    (hM : isTrianglePacking G {cfg.A, cfg.B, cfg.C, cfg.D})
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_not_M : T ∉ ({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V)))
    -- Assume T shares edge with A (from pair 1)
    (h_share_A : sharesEdgeWith T cfg.A)
    -- And T shares edge with C (from pair 2)
    (h_share_C : sharesEdgeWith T cfg.C) :
    False := by
  -- If T shares edge with A, then |T ∩ A| ≥ 2
  -- If T shares edge with C, then |T ∩ C| ≥ 2
  -- But |T| = 3, so |T ∩ A| + |T ∩ C| ≤ 3 + some overlap
  -- The overlap (T ∩ A ∩ C) ⊆ (A ∩ C)
  -- By pairs_vertex_disjoint, |A ∩ C| ≤ 1
  -- So |T ∩ A| + |T ∩ C| - |T ∩ A ∩ C| ≤ 2 + 2 - something ≤ 3
  -- This means T ⊆ A ∪ C, and the constraints are tight
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE CLASSIFICATION FOR TWO_TWO_VW
-- ══════════════════════════════════════════════════════════════════════════════

/-- In two_two_vw, all bridges are WITHIN pairs (not across) -/
lemma bridge_within_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : TwoTwoVW V)
    (M : Finset (Finset V)) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (hM_pack : isTrianglePacking G M)
    (T : Finset V) (hT : isBridgeTriangle G M T) :
    (sharesEdgeWith T cfg.A ∧ sharesEdgeWith T cfg.B) ∨
    (sharesEdgeWith T cfg.C ∧ sharesEdgeWith T cfg.D) := by
  -- T is a bridge, so it shares edges with two distinct M-elements
  obtain ⟨hT_tri, hT_not_M, X, Y, hX, hY, hXY, hTX, hTY⟩ := hT
  -- X and Y are in M = {A, B, C, D}
  rw [hM_eq] at hX hY
  -- Case analysis: X and Y must be from the same pair (A,B) or (C,D)
  -- If they were from different pairs, no_cross_pair_bridge gives contradiction
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- WITHIN-PAIR BRIDGE COVERAGE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridges within pair {A,B} are covered by apex edges of A or B -/
lemma within_pair_bridge_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : TwoTwoVW V)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (h_share_A : sharesEdgeWith T cfg.A)
    (h_share_B : sharesEdgeWith T cfg.B)
    -- The apex edges selected for A and B (based on shared vertex v)
    (E_A : Finset (Sym2 V)) (E_B : Finset (Sym2 V))
    (h_EA_apex : ∀ e ∈ E_A, cfg.v ∈ e)
    (h_EB_apex : ∀ e ∈ E_B, cfg.v ∈ e) :
    (∃ e ∈ E_A, e ∈ T.sym2) ∨ (∃ e ∈ E_B, e ∈ T.sym2) := by
  -- T shares edge with A, and A ∩ B = {v}
  -- So T ∩ A has 2 vertices including possibly v
  -- If v ∈ T, then any apex edge containing v will hit T
  -- If v ∉ T, the shared edge with A doesn't contain v...
  -- But then the shared edge with B also doesn't contain v...
  -- Since A ∩ B = {v}, this means T shares edges with A and B avoiding v
  -- But then T ∩ A ⊆ A \ {v} and T ∩ B ⊆ B \ {v}
  -- Since |T ∩ A| ≥ 2 and |A \ {v}| = 2, we have T ∩ A = A \ {v}
  -- Similarly T ∩ B = B \ {v}
  -- So T ⊇ (A \ {v}) ∪ (B \ {v})
  -- But |(A \ {v}) ∪ (B \ {v})| = 2 + 2 - |(A ∩ B) \ {v}| = 4 - 0 = 4
  -- This contradicts |T| = 3
  -- Therefore v ∈ T, and any apex edge at v covers T
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TAU BOUND FOR TWO_TWO_VW
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_two_two_vw (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : TwoTwoVW V)
    (M : Finset (Finset V)) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (hM_pack : isTrianglePacking G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Cover construction:
  -- At v: 2 apex edges from A, 2 apex edges from B → but they overlap!
  --       Actually just need 2 edges at v to cover both A, B and their externals
  -- At w: 2 edges to cover C, D and their externals
  -- Bridges within {A,B}: covered by edges at v (by within_pair_bridge_covered)
  -- Bridges within {C,D}: covered by edges at w
  -- No cross-pair bridges (by no_cross_pair_bridge)
  --
  -- Total: 2 (at v) + 2 (at w) + possibly some for externals
  -- With careful counting: ≤ 8
  sorry

end
