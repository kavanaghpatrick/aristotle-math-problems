/-
  slot542: BRIDGE APEX CONSTRAINT (integrated scaffolding from slots 535, 538, 539)

  GOAL: For bridge B between X,Y in a ν=4 packing, apex_X ∈ B ∨ apex_Y ∈ B.
  PROOF: By contradiction. If both apexes away, apex-edges miss B, B uncovered.
  10+ proven helpers included.
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- DEFINITIONS

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

-- PROVEN HELPER: sharesEdgeWith ↔ card_inter (from slot535, slot539)

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- PROVEN HELPER: triangle card (from slot539)

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

-- PROVEN HELPER: triangle decomposition (from slot535)

lemma triangle_card_eq_three (T : Finset V) (hT : T.card = 3) :
    ∃ a b c : V, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ T = {a, b, c} := by
  obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := Finset.card_eq_three.mp hT
  exact ⟨a, b, c, by rw [h_eq]; simp, by rw [h_eq]; simp, by rw [h_eq]; simp,
         hab, hac, hbc, h_eq⟩

-- PROVEN: bridge_shared_edge_card (from slot539, NOW FIXED)

/--
PROVIDED SOLUTION:
1. sharesEdgeWith gives |B ∩ X| ≥ 2
2. Both B and X have card 3, so |B ∩ X| ≤ 3
3. If |B ∩ X| = 3, then B ∩ X = B = X (both card 3), contradicting B ≠ X
4. Therefore |B ∩ X| = 2
-/
lemma bridge_shared_edge_card (B X : Finset V)
    (hB_card : B.card = 3) (hX_card : X.card = 3)
    (h_share : sharesEdgeWith B X) (hBX : B ≠ X) :
    (B ∩ X).card = 2 := by
  have h_ge : (B ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B X |>.mp h_share
  have h_le : (B ∩ X).card ≤ 2 := by
    by_contra h
    push_neg at h
    have h_inter_le_B : (B ∩ X).card ≤ B.card := Finset.card_le_card Finset.inter_subset_left
    have h_inter_le_X : (B ∩ X).card ≤ X.card := Finset.card_le_card Finset.inter_subset_right
    rw [hB_card] at h_inter_le_B
    rw [hX_card] at h_inter_le_X
    -- |B ∩ X| ≥ 3 and ≤ 3, so = 3
    have h_eq_3 : (B ∩ X).card = 3 := by omega
    -- B ∩ X has same card as B, so B ⊆ B ∩ X ⊆ X, giving B = X
    have hB_sub_X : B ⊆ X := by
      intro x hx
      have : (B ∩ X).card = B.card := by rw [h_eq_3, hB_card]
      have hBX_eq : B ∩ X = B := Finset.eq_of_superset_of_card_le Finset.inter_subset_left (by omega)
      exact Finset.mem_of_mem_inter_right (hBX_eq ▸ hx)
    have : B = X := Finset.eq_of_subset_of_card_le hB_sub_X (by rw [hB_card, hX_card])
    exact hBX this
  omega

-- PROVEN: apex_is_unique_outside (from slot539)

lemma apex_is_unique_outside (X B : Finset V)
    (hX_card : X.card = 3) (h_inter_card : (B ∩ X).card = 2) :
    ∃! v, v ∈ X ∧ v ∉ B := by
  have h_sdiff : (X \ (B ∩ X)).card = 1 := by
    rw [Finset.card_sdiff (Finset.inter_subset_right), hX_card, h_inter_card]
  obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.mp h_sdiff
  use v
  constructor
  · constructor
    · have : v ∈ X \ (B ∩ X) := by rw [hv_eq]; exact Finset.mem_singleton_self v
      exact Finset.mem_of_mem_sdiff this
    · have : v ∈ X \ (B ∩ X) := by rw [hv_eq]; exact Finset.mem_singleton_self v
      intro hv_B
      have hv_inter : v ∈ B ∩ X := Finset.mem_inter.mpr ⟨hv_B, Finset.mem_of_mem_sdiff this⟩
      exact Finset.not_mem_sdiff_of_mem_right hv_inter this
  · intro w ⟨hw_X, hw_not_B⟩
    have hw_sdiff : w ∈ X \ (B ∩ X) := by
      rw [Finset.mem_sdiff, Finset.mem_inter]
      exact ⟨hw_X, fun ⟨hw_B, _⟩ => hw_not_B hw_B⟩
    rw [hv_eq, Finset.mem_singleton] at hw_sdiff
    exact hw_sdiff

-- PROVEN: apex_away_misses_bridge (from slot539)

/-- If apex ∉ B, then all edges containing apex miss B.sym2 -/
lemma apex_away_misses_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (X B : Finset V) (hX_tri : X ∈ G.cliqueFinset 3) (hB_tri : B ∈ G.cliqueFinset 3)
    (h_share : sharesEdgeWith B X)
    (apex_X : V) (h_apex_in_X : apex_X ∈ X) (h_apex_not_B : apex_X ∉ B) :
    ∀ e : Sym2 V, apex_X ∈ e → e ∈ X.sym2 → e ∉ B.sym2 := by
  intro e he_apex he_X
  intro he_B
  rw [Finset.mem_sym2_iff] at he_B
  have : apex_X ∈ B := he_B apex_X he_apex
  exact h_apex_not_B this

-- PROVEN: apex_selection_misses_bridge (from slot535)

/-- If apex ∉ Br, then neither apex-edge is in Br.sym2 -/
lemma apex_selection_misses_bridge (X Br : Finset V)
    (hX_card : X.card = 3)
    (h_share : (X ∩ Br).card = 2)
    (apex : V) (h_apex_in_X : apex ∈ X) (h_apex_not_Br : apex ∉ Br)
    (u v : V) (h_X_eq : X = {apex, u, v}) (h_u_in_Br : u ∈ Br) (h_v_in_Br : v ∈ Br) :
    s(apex, u) ∉ Br.sym2 ∧ s(apex, v) ∉ Br.sym2 := by
  constructor
  · intro h_in
    rw [Finset.mem_sym2_iff] at h_in
    have h1 : apex ∈ Br := h_in apex (Sym2.mem_iff.mpr (Or.inl rfl))
    exact h_apex_not_Br h1
  · intro h_in
    rw [Finset.mem_sym2_iff] at h_in
    have h1 : apex ∈ Br := h_in apex (Sym2.mem_iff.mpr (Or.inl rfl))
    exact h_apex_not_Br h1

-- PROVEN: apex_selection_not_bridge_edge (from slot535)

lemma apex_selection_not_bridge_edge (X Br : Finset V)
    (hX_card : X.card = 3) (hBr_card : Br.card = 3)
    (h_share : (X ∩ Br).card = 2)
    (apex : V) (h_apex_in_X : apex ∈ X) (h_apex_not_Br : apex ∉ Br) :
    ∃ u v : V, u ∈ X ∧ v ∈ X ∧ u ∈ Br ∧ v ∈ Br ∧ u ≠ v ∧
              X ∩ Br = {u, v} ∧
              s(apex, u) ≠ s(u, v) ∧ s(apex, v) ≠ s(u, v) := by
  obtain ⟨u', v', huv', h_inter_eq⟩ := Finset.card_eq_two.mp h_share
  have hu'_X : u' ∈ X := by
    have : u' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_self _ _
    exact Finset.mem_of_mem_inter_left this
  have hv'_X : v' ∈ X := by
    have : v' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact Finset.mem_of_mem_inter_left this
  have hu'_Br : u' ∈ Br := by
    have : u' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_self _ _
    exact Finset.mem_of_mem_inter_right this
  have hv'_Br : v' ∈ Br := by
    have : v' ∈ X ∩ Br := by rw [h_inter_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact Finset.mem_of_mem_inter_right this
  use u', v', hu'_X, hv'_X, hu'_Br, hv'_Br, huv', h_inter_eq
  have h_apex_ne_u : apex ≠ u' := by
    intro h_eq; rw [h_eq] at h_apex_not_Br; exact h_apex_not_Br hu'_Br
  have h_apex_ne_v : apex ≠ v' := by
    intro h_eq; rw [h_eq] at h_apex_not_Br; exact h_apex_not_Br hv'_Br
  constructor
  · intro h_eq
    simp only [Sym2.eq_iff] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact h_apex_ne_v rfl; exact h_apex_ne_u rfl]
  · intro h_eq
    simp only [Sym2.eq_iff] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact h_apex_ne_u rfl; exact h_apex_ne_v rfl]

-- PROVEN: bridge_not_in_packing

lemma bridge_not_in_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (B : Finset V) (hB : isBridgeTriangle G M B) :
    B ∉ M :=
  hB.2.1

-- PROVEN: bridge_ne_packing_element

lemma bridge_ne_packing_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (B X : Finset V)
    (hB : isBridgeTriangle G M B) (hX : X ∈ M) : B ≠ X :=
  fun h => hB.2.1 (h ▸ hX)

-- PROVEN: packing_inter_card_le_one

lemma packing_inter_card_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y) :
    (X ∩ Y).card ≤ 1 :=
  hM.2 hX hY hXY

-- MAIN THEOREM: At least one apex must be in B

/--
PROVIDED SOLUTION:
1. Assume for contradiction: apex_X ∉ B AND apex_Y ∉ B
2. B shares edges with X and Y: |B ∩ X| = 2, |B ∩ Y| = 2 (by bridge_shared_edge_card)
3. apex_X is the unique vertex of X outside B (by apex_is_unique_outside), similarly apex_Y for Y
4. All apex_X-edges from X miss B (by apex_away_misses_bridge)
5. All apex_Y-edges from Y miss B (similarly)
6. B is a triangle in G but no apex-edge from any M-element hits B
7. Replace X with B in the packing: since B shares 2 vertices with X but not the apex,
   we can form a new triangle using apex_X with other vertices, giving |M'| = 5
8. This contradicts ν = 4, so apex_X ∈ B ∨ apex_Y ∈ B
-/
theorem bridge_has_apex_in_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (B : Finset V) (hB : isBridgeTriangle G M B)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (h_share_X : sharesEdgeWith B X) (h_share_Y : sharesEdgeWith B Y)
    (apex : Finset V → V)
    (h_apex : ∀ Z ∈ M, apex Z ∈ Z) :
    apex X ∈ B ∨ apex Y ∈ B := by
  -- Proof by contradiction
  by_contra h
  push_neg at h
  obtain ⟨h_apex_X_not_B, h_apex_Y_not_B⟩ := h
  -- Derive B ≠ X and B ≠ Y (B ∉ M but X, Y ∈ M)
  have hB_not_M : B ∉ M := hB.2.1
  have hBX : B ≠ X := fun heq => hB_not_M (heq ▸ hX)
  have hBY : B ≠ Y := fun heq => hB_not_M (heq ▸ hY)
  -- Card facts
  have hX_card : X.card = 3 := triangle_card_three G X (hM.1.1 hX)
  have hY_card : Y.card = 3 := triangle_card_three G Y (hM.1.1 hY)
  have hB_card : B.card = 3 := triangle_card_three G B hB.1
  -- Shared edge cardinalities
  have h_BX_card : (B ∩ X).card = 2 := bridge_shared_edge_card B X hB_card hX_card h_share_X hBX
  have h_BY_card : (B ∩ Y).card = 2 := bridge_shared_edge_card B Y hB_card hY_card h_share_Y hBY
  -- Both apexes are the unique vertex outside B
  have h_apex_X_unique := apex_is_unique_outside X B hX_card h_BX_card
  have h_apex_Y_unique := apex_is_unique_outside Y B hY_card h_BY_card
  -- Apex edges from X miss B
  have h_X_miss := apex_away_misses_bridge G X B (hM.1.1 hX) hB.1 h_share_X
    (apex X) (h_apex X hX) h_apex_X_not_B
  -- Apex edges from Y miss B
  have h_Y_miss := apex_away_misses_bridge G Y B (hM.1.1 hY) hB.1 h_share_Y
    (apex Y) (h_apex Y hY) h_apex_Y_not_B
  -- Now: B is uncovered. Both X's and Y's apex-edges miss B.
  -- Use ν=4 to derive contradiction via 5-packing construction
  sorry

end
