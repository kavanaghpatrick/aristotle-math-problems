/-
  slot426_tau_le_8_assembly.lean

  FINAL ASSEMBLY: τ ≤ 8 for PATH_4 via coordinated spine-priority selection

  PROVEN COMPONENTS:
  - slot423: 2 REAL edges cover S_e (externals to single element)
  - slot441: Bridges contain shared spine vertex (bridge_contains_shared)
  - slot425: Spine edge covers ALL adjacent bridges (spine_edge_covers_adjacent_bridges)

  MULTI-AGENT CONSENSUS (Grok, Gemini, Codex):
  - Gap is REAL: Independent 2-per-element selection can miss bridges
  - Solution: Spine Priority - middle elements pick spine edge first

  TIER: 2-3 (assembly of proven components)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot441, slot425)
-- ══════════════════════════════════════════════════════════════════════════════

/-- slot441: Bridges contain the shared vertex -/
theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    ext x; simp only [mem_inter, mem_singleton]; constructor
    · intro ⟨⟨hxT, hxE⟩, _, hxF⟩
      have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE, hxF⟩
      rw [hEF] at hx_both
      exact ⟨hxT, mem_singleton.mp hx_both⟩
    · intro ⟨hxT, hxv⟩
      have hv_mem : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      rw [hxv]
      exact ⟨⟨hxT, (mem_inter.mp hv_mem).1⟩, hxT, (mem_inter.mp hv_mem).2⟩
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx; simp only [mem_union, mem_inter] at hx
    cases hx with | inl h => exact h.1 | inr h => exact h.1
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
      calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
        _ = 3 := hT_card
    omega
  rw [card_pos] at h_pos
  obtain ⟨x, hx⟩ := h_pos
  simp only [mem_inter, mem_singleton] at hx
  exact hx.2 ▸ hx.1

/-- slot425: Spine edge covers adjacent bridges -/
theorem spine_edge_covers_adjacent_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (v₁ v₂ : V)
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hBridge : (2 ≤ (T ∩ A).card ∧ 2 ≤ (T ∩ B).card) ∨
               (2 ≤ (T ∩ B).card ∧ 2 ≤ (T ∩ C).card)) :
    v₁ ∈ T ∨ v₂ ∈ T := by
  cases hBridge with
  | inl hAB_bridge => exact Or.inl (bridge_contains_shared G A B v₁ hAB T hT hAB_bridge.1 hAB_bridge.2)
  | inr hBC_bridge => exact Or.inr (bridge_contains_shared G B C v₂ hBC T hT hBC_bridge.1 hBC_bridge.2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- PATH_4 configuration: 4 triangles sharing spine vertices -/
structure PATH4 (G : SimpleGraph V) [DecidableRel G.Adj] where
  A B C D : Finset V
  v₁ v₂ v₃ : V
  a₁ a₂ b c d₁ d₂ : V
  -- Triangle membership
  hA : A ∈ G.cliqueFinset 3
  hB : B ∈ G.cliqueFinset 3
  hC : C ∈ G.cliqueFinset 3
  hD : D ∈ G.cliqueFinset 3
  -- Triangle vertices
  hA_verts : A = {a₁, a₂, v₁}
  hB_verts : B = {v₁, b, v₂}
  hC_verts : C = {v₂, c, v₃}
  hD_verts : D = {v₃, d₁, d₂}
  -- Spine intersections (exactly one shared vertex each)
  hAB : A ∩ B = {v₁}
  hBC : B ∩ C = {v₂}
  hCD : C ∩ D = {v₃}
  -- Edge disjointness (packing property)
  hAB_disj : (A ∩ B).card ≤ 1
  hAC_disj : (A ∩ C).card ≤ 1
  hAD_disj : (A ∩ D).card ≤ 1
  hBC_disj : (B ∩ C).card ≤ 1
  hBD_disj : (B ∩ D).card ≤ 1
  hCD_disj : (C ∩ D).card ≤ 1

-- ══════════════════════════════════════════════════════════════════════════════
-- TRIANGLE CLASSIFICATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle is a packing element -/
def isPacking (P : PATH4 G) (T : Finset V) : Prop :=
  T = P.A ∨ T = P.B ∨ T = P.C ∨ T = P.D

/-- A triangle is external to element E (shares edge with E only) -/
def isExternal (G : SimpleGraph V) [DecidableRel G.Adj] (P : PATH4 G)
    (E T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  2 ≤ (T ∩ E).card ∧
  T ≠ E ∧
  (∀ F, isPacking P F → F ≠ E → (T ∩ F).card ≤ 1)

/-- A triangle is a bridge between E and F -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  2 ≤ (T ∩ E).card ∧
  2 ≤ (T ∩ F).card ∧
  T ≠ E ∧ T ≠ F

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edge from triangle: given vertices a, b, c, return edge s(a,b) -/
def triEdge (a b : V) : Sym2 V := s(a, b)

/-- Spine edge of middle element B: edge connecting the two shared vertices -/
def spineEdge (P : PATH4 G) : Sym2 V := s(P.v₁, P.v₂)

/-- Second spine edge (for C) -/
def spineEdge2 (P : PATH4 G) : Sym2 V := s(P.v₂, P.v₃)

/--
  MAIN THEOREM: τ ≤ 8 for PATH_4

  Cover construction via spine-priority:
  - A: 2 edges (one must include v₁ for bridges)
  - B: spine {v₁,v₂} + {v₁,b} = 2 edges (covers bridges to A and C)
  - C: spine {v₂,v₃} + {v₂,c} = 2 edges (covers bridges to B and D)
  - D: 2 edges (one must include v₃ for bridges)

  Total: 8 edges

  PROOF SKETCH:
  1. Packing triangles A,B,C,D: covered by their own edges (trivial)
  2. External to A only: covered by A's 2 edges (slot423)
  3. External to D only: covered by D's 2 edges (slot423)
  4. External to B only: covered by B's 2 edges (slot423)
  5. External to C only: covered by C's 2 edges (slot423)
  6. Bridge A-B: contains v₁ (slot441), so spine {v₁,v₂} or A's v₁-edge hits it
  7. Bridge B-C: contains v₂ (slot441), so spine {v₁,v₂} or {v₂,v₃} hits it
  8. Bridge C-D: contains v₃ (slot441), so spine {v₂,v₃} or D's v₃-edge hits it
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj] (P : PATH4 G)
    (hAdj_v1v2 : G.Adj P.v₁ P.v₂)
    (hAdj_v2v3 : G.Adj P.v₂ P.v₃)
    (hAdj_v1b : G.Adj P.v₁ P.b)
    (hAdj_v2c : G.Adj P.v₂ P.c) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  -- Construct the 8-edge cover using spine-priority
  -- A: {a₁,v₁}, {a₂,v₁}  (both contain v₁ for bridge coverage)
  -- B: {v₁,v₂}, {v₁,b}   (spine + one other)
  -- C: {v₂,v₃}, {v₂,c}   (spine + one other)
  -- D: {v₃,d₁}, {v₃,d₂}  (both contain v₃ for bridge coverage)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge coverage via spine
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any bridge between adjacent elements is covered by spine edges -/
theorem bridge_covered_by_spine (G : SimpleGraph V) [DecidableRel G.Adj] (P : PATH4 G)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hBridge_AB : isBridge G P.A P.B T) :
    P.v₁ ∈ T := by
  exact bridge_contains_shared G P.A P.B P.v₁ P.hAB T hT hBridge_AB.2.1 hBridge_AB.2.2.1

theorem bridge_BC_covered (G : SimpleGraph V) [DecidableRel G.Adj] (P : PATH4 G)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hBridge_BC : isBridge G P.B P.C T) :
    P.v₂ ∈ T := by
  exact bridge_contains_shared G P.B P.C P.v₂ P.hBC T hT hBridge_BC.2.1 hBridge_BC.2.2.1

theorem bridge_CD_covered (G : SimpleGraph V) [DecidableRel G.Adj] (P : PATH4 G)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hBridge_CD : isBridge G P.C P.D T) :
    P.v₃ ∈ T := by
  exact bridge_contains_shared G P.C P.D P.v₃ P.hCD T hT hBridge_CD.2.1 hBridge_CD.2.2.1

end
