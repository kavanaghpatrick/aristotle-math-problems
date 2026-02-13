/-
  slot534: FIVE PACKING EXCHANGE LEMMA

  Core lemma: If a bridge B is "missed" by the apex selections of both
  neighboring M-elements, then we can construct a 5-packing.

  This is the HEART of the bad bridge argument.

  PROOF STRATEGY (Exchange Argument):
  Let M = {A, B, C, D} be a 4-packing.
  Let Br be a bridge triangle sharing edges with A and B.

  If A's apex is away from Br and B's apex is away from Br, then:
  1. A = {a, p, q} where apex a ∉ Br, and {p,q} ⊆ Br
  2. B = {b, r, s} where apex b ∉ Br, and {r,s} ⊆ Br
  3. Br = {p, q, ...} ∩ {r, s, ...}

  The key insight: Since a ∉ Br and b ∉ Br, the triangle Br is "free"
  to join a modified packing.

  We show: M' = {Br, C, D, T₁, T₂} forms a 5-packing for suitable T₁, T₂
  constructed from vertices a, b and the graph structure.
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

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

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

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX STRUCTURE OF BRIDGE CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- When a bridge Br shares edge with X, we can decompose X as {apex, u, v}
    where {u, v} ⊆ Br -/
structure BridgeNeighborConfig (V : Type*) where
  X : Finset V        -- The M-element
  Br : Finset V       -- The bridge triangle
  apex : V            -- Apex of X (vertex not in Br)
  u : V               -- First vertex of shared edge
  v : V               -- Second vertex of shared edge
  h_X_eq : X = {apex, u, v}
  h_apex_not_Br : apex ∉ Br
  h_u_in_Br : u ∈ Br
  h_v_in_Br : v ∈ Br
  h_all_distinct : apex ≠ u ∧ apex ≠ v ∧ u ≠ v

/-- Extract the configuration when apex is away from bridge -/
lemma bridge_neighbor_config_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Br : Finset V) (hX_tri : X ∈ G.cliqueFinset 3) (hBr_tri : Br ∈ G.cliqueFinset 3)
    (h_share : sharesEdgeWith Br X) (apex : V) (h_apex_in : apex ∈ X) (h_apex_not_Br : apex ∉ Br) :
    ∃ u v : V, u ∈ X ∧ v ∈ X ∧ u ∈ Br ∧ v ∈ Br ∧ u ≠ v ∧
              apex ≠ u ∧ apex ≠ v ∧ X = {apex, u, v} := by
  -- X has 3 elements, apex is one of them
  have hX_card : X.card = 3 := triangle_card_three G X hX_tri
  -- The shared edge gives us u, v ∈ X ∩ Br
  obtain ⟨u', v', huv', hu'_Br, hv'_Br, hu'_X, hv'_X⟩ := h_share
  -- Since apex ∉ Br, apex ≠ u' and apex ≠ v'
  have h_apex_ne_u : apex ≠ u' := fun h => h_apex_not_Br (h ▸ hu'_Br)
  have h_apex_ne_v : apex ≠ v' := fun h => h_apex_not_Br (h ▸ hv'_Br)
  -- X = {apex, u', v'}
  have h_X_eq : X = {apex, u', v'} := by
    ext x
    constructor
    · intro hx
      by_cases hx_apex : x = apex
      · simp [hx_apex]
      · by_cases hx_u : x = u'
        · simp [hx_u]
        · by_cases hx_v : x = v'
          · simp [hx_v]
          · -- x ∈ X, x ≠ apex, u', v' → contradicts |X| = 3
            have h_sub : {apex, u', v'} ⊆ X := by
              intro y hy
              simp at hy
              rcases hy with rfl | rfl | rfl <;> assumption
            have h_card : ({apex, u', v'} : Finset V).card = 3 := by
              rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
                  Finset.card_singleton]
              · simp [huv']
              · simp [h_apex_ne_u, h_apex_ne_v]
            have h_eq : X = {apex, u', v'} := by
              apply Finset.eq_of_subset_of_card_le h_sub
              rw [hX_card, h_card]
            rw [h_eq] at hx
            simp at hx
            rcases hx with rfl | rfl | rfl <;> contradiction
    · intro hx
      simp at hx
      rcases hx with rfl | rfl | rfl <;> assumption
  exact ⟨u', v', hu'_X, hv'_X, hu'_Br, hv'_Br, huv', h_apex_ne_u, h_apex_ne_v, h_X_eq⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- THE EXCHANGE LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Given M = {A, B, C, D} and bridge Br between A and B with both apexes away:
- A = {a, p, q} with a ∉ Br, {p, q} ⊆ Br
- B = {b, r, s} with b ∉ Br, {r, s} ⊆ Br
- Br shares {p, q} with A and {r, s} with B

Case analysis on Br structure:
1. If Br = {p, q, x} for some x:
   - Must have {r, s} ⊆ {p, q, x}, so {r, s} = some 2-subset

2. The vertices a and b are "free" (not in Br)
   - If ∃ triangle T containing a and edge-disjoint from M \ {A}, add it
   - Similarly for b

3. Key observation: The edge {a, ?} from A and {b, ?} from B
   are NOT in Br, so Br is edge-disjoint from triangles using these edges

4. Construct M' = {Br} ∪ (M \ {A, B}) ∪ {new triangles using a, b}
   This gives |M'| ≥ 5 if we can find the new triangles

5. The existence of new triangles follows from graph connectivity
   and the fact that a, b have edges in G (they were in triangles A, B)
-/

lemma five_packing_from_missed_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (Br : Finset V) (hBr : isBridgeTriangle G M Br)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (h_share_A : sharesEdgeWith Br A) (h_share_B : sharesEdgeWith Br B)
    (a b : V)
    (ha_in_A : a ∈ A) (ha_not_Br : a ∉ Br)
    (hb_in_B : b ∈ B) (hb_not_Br : b ∉ Br)
    -- Additional hypothesis: a and b form triangles with some of M's edges
    (h_a_has_triangle : ∃ T ∈ G.cliqueFinset 3, a ∈ T ∧ (T ∩ Br).card ≤ 1 ∧
                        ∀ X ∈ M, X ≠ A → (T ∩ X).card ≤ 1)
    (h_b_has_triangle : ∃ T ∈ G.cliqueFinset 3, b ∈ T ∧ (T ∩ Br).card ≤ 1 ∧
                        ∀ X ∈ M, X ≠ B → (T ∩ X).card ≤ 1) :
    ∃ P : Finset (Finset V), isTrianglePacking G P ∧ P.card ≥ 5 := by
  -- Get the other elements of M (C and D)
  have h_other_exists : ∃ C D : Finset V, C ∈ M ∧ D ∈ M ∧ C ≠ A ∧ C ≠ B ∧ D ≠ A ∧ D ≠ B ∧ C ≠ D := by
    -- M has 4 elements, A and B are 2 of them
    sorry
  obtain ⟨C, D, hC, hD, hCA, hCB, hDA, hDB, hCD⟩ := h_other_exists

  -- Get the triangles from hypotheses
  obtain ⟨T_a, hTa_tri, ha_in_Ta, hTa_Br, hTa_M⟩ := h_a_has_triangle
  obtain ⟨T_b, hTb_tri, hb_in_Tb, hTb_Br, hTb_M⟩ := h_b_has_triangle

  -- Construct M' = {Br, C, D, T_a, T_b}
  let M' : Finset (Finset V) := {Br, C, D, T_a, T_b}

  -- Show M' is a packing
  use M'
  constructor
  · -- isTrianglePacking G M'
    constructor
    · -- All elements are triangles
      intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl
      · exact hBr.1
      · exact hM.1.1 hC
      · exact hM.1.1 hD
      · exact hTa_tri
      · exact hTb_tri
    · -- Pairwise edge-disjoint
      intro X hX Y hY hXY
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
      sorry -- Case analysis on which elements X and Y are
  · -- |M'| ≥ 5
    sorry -- Need to show the 5 elements are distinct

end
