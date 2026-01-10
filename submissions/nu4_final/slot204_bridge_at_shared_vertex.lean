/-
Tuza ν=4: Bridge at Shared Vertex (Slot 204)

GOAL: Bridges between M-elements contain their shared vertex.

DEFINITION: A bridge between A and B is a triangle T ∉ M that shares edge
with BOTH A and B but is not external to either (i.e., shares with ≥2 M-elements).

KEY INSIGHT (from FALSE_LEMMAS.md Pattern 3):
  - Bridges share vertices with A and B but may not share edges with S_A or S_B
  - We must handle bridges separately from externals

LEMMA: If A ∩ B = {v} (cycle_4 shared vertex), then any bridge T between A,B
must contain v.

PROOF:
  - T shares edge with A: T ∩ A ≥ 2, so T contains ≥2 vertices of A = {v, a₁, a₂}
  - T shares edge with B: T ∩ B ≥ 2, so T contains ≥2 vertices of B = {v, b₁, b₂}
  - A ∩ B = {v}, so v is the ONLY common vertex
  - T has 3 vertices total
  - If T contained 2 vertices from A \ {v} = {a₁, a₂} and 2 from B \ {v} = {b₁, b₂},
    that's 4 vertices (impossible for 3-set)
  - So T must contain v
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

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

/-- A bridge between A and B: shares edge with both -/
def isBridgeBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧ sharesEdgeWith t B

def bridgesBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isBridgeBetween G M A B)

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMA: Bridge contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- If A ∩ B = {v} and T shares edge with both A and B, then v ∈ T -/
theorem bridge_contains_shared_vertex (A B T : Finset V) (v : V)
    (hA : A.card = 3) (hB : B.card = 3) (hT : T.card = 3)
    (h_inter : A ∩ B = {v})
    (h_T_A : sharesEdgeWith T A)
    (h_T_B : sharesEdgeWith T B) :
    v ∈ T := by
  -- T ∩ A ≥ 2 and T ∩ B ≥ 2
  obtain ⟨u₁, w₁, huw₁, hu₁_T, hw₁_T, hu₁_A, hw₁_A⟩ := h_T_A
  obtain ⟨u₂, w₂, huw₂, hu₂_T, hw₂_T, hu₂_B, hw₂_B⟩ := h_T_B

  -- {u₁, w₁} ⊆ T ∩ A and {u₂, w₂} ⊆ T ∩ B
  have h_TA_card : (T ∩ A).card ≥ 2 := by
    calc (T ∩ A).card ≥ ({u₁, w₁} : Finset V).card := by
           apply Finset.card_le_card
           intro x hx; simp at hx; rcases hx with rfl | rfl
           · exact Finset.mem_inter.mpr ⟨hu₁_T, hu₁_A⟩
           · exact Finset.mem_inter.mpr ⟨hw₁_T, hw₁_A⟩
       _ = 2 := by simp [huw₁]

  have h_TB_card : (T ∩ B).card ≥ 2 := by
    calc (T ∩ B).card ≥ ({u₂, w₂} : Finset V).card := by
           apply Finset.card_le_card
           intro x hx; simp at hx; rcases hx with rfl | rfl
           · exact Finset.mem_inter.mpr ⟨hu₂_T, hu₂_B⟩
           · exact Finset.mem_inter.mpr ⟨hw₂_T, hw₂_B⟩
       _ = 2 := by simp [huw₂]

  -- A \ B = A \ {v} has card 2 (since A ∩ B = {v} and |A| = 3)
  have h_A_minus_B : (A \ B).card = 2 := by
    have hv_A : v ∈ A := by
      have : v ∈ A ∩ B := by rw [h_inter]; simp
      exact Finset.mem_inter.mp this |>.1
    calc (A \ B).card = A.card - (A ∩ B).card := by
           rw [Finset.card_sdiff (Finset.inter_subset_left)]
       _ = 3 - 1 := by rw [hA, h_inter]; simp
       _ = 2 := by norm_num

  -- Similarly for B \ A
  have h_B_minus_A : (B \ A).card = 2 := by
    have hv_B : v ∈ B := by
      have : v ∈ A ∩ B := by rw [h_inter]; simp
      exact Finset.mem_inter.mp this |>.2
    calc (B \ A).card = B.card - (B ∩ A).card := by
           rw [Finset.card_sdiff (Finset.inter_subset_left)]
       _ = 3 - 1 := by rw [hB, Finset.inter_comm, h_inter]; simp
       _ = 2 := by norm_num

  -- Key insight: T has 3 vertices
  -- T ∩ A ≥ 2 and T ∩ B ≥ 2
  -- If v ∉ T, then T ∩ A ⊆ A \ {v} = A \ B (since A ∩ B = {v})
  -- and T ∩ B ⊆ B \ {v} = B \ A
  -- So T ⊇ (T ∩ A) ∪ (T ∩ B) where (T ∩ A) ∩ (T ∩ B) ⊆ T ∩ (A ∩ B) = T ∩ {v} = ∅
  -- This means |T| ≥ |T ∩ A| + |T ∩ B| ≥ 2 + 2 = 4, contradiction with |T| = 3

  by_contra hv_not_T
  -- T ∩ (A ∩ B) = T ∩ {v} = ∅ (since v ∉ T)
  have h_TAB_empty : T ∩ (A ∩ B) = ∅ := by
    rw [h_inter]
    simp [hv_not_T]
  -- (T ∩ A) ∩ (T ∩ B) ⊆ T ∩ (A ∩ B) = ∅
  have h_disjoint : Disjoint (T ∩ A) (T ∩ B) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    calc (T ∩ A) ∩ (T ∩ B) = T ∩ A ∩ B := by
           ext x; simp [Finset.mem_inter]; tauto
       _ = T ∩ (A ∩ B) := by ext x; simp [Finset.mem_inter]; tauto
       _ = ∅ := h_TAB_empty
  -- |T| ≥ |(T ∩ A) ∪ (T ∩ B)| = |T ∩ A| + |T ∩ B| ≥ 2 + 2 = 4
  have h_card_ge_4 : T.card ≥ 4 := by
    calc T.card ≥ ((T ∩ A) ∪ (T ∩ B)).card := Finset.card_le_card (by
           intro x hx; simp at hx; rcases hx with ⟨hxT, _⟩ | ⟨hxT, _⟩ <;> exact hxT)
       _ = (T ∩ A).card + (T ∩ B).card := by
           rw [Finset.card_union_of_disjoint h_disjoint]
       _ ≥ 2 + 2 := by omega
       _ = 4 := by norm_num
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Bridges are covered by spokes from shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridges between A and B are covered by spokes from their shared vertex -/
theorem bridge_covered_by_spoke (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T : Finset V) (v : V)
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hT_clique : T ∈ G.cliqueFinset 3)
    (h_inter : A ∩ B = {v})
    (h_T_A : sharesEdgeWith T A)
    (h_T_B : sharesEdgeWith T B) :
    ∃ x : V, (x ∈ A ∨ x ∈ B) ∧ x ≠ v ∧ s(v, x) ∈ T.sym2 := by
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).2
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hB_clique).2
  have hT_card : T.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hT_clique).2
  -- v ∈ T by bridge_contains_shared_vertex
  have hv_T := bridge_contains_shared_vertex A B T v hA_card hB_card hT_card h_inter h_T_A h_T_B
  -- T = {v, x, y} for some x, y
  -- T shares edge with A: so T ∩ A ≥ 2
  -- Since v ∈ A ∩ T, one of x, y is also in A (call it x)
  -- Then s(v, x) ∈ T.sym2 with x ∈ A
  obtain ⟨u, w, huw, hu_T, hw_T, hu_A, hw_A⟩ := h_T_A
  -- {u, w} ⊆ T ∩ A, and v ∈ A ∩ T
  have hv_A : v ∈ A := by
    rw [← h_inter]; exact Finset.mem_inter.mpr ⟨rfl, by rw [h_inter]; simp⟩
  -- If u = v, use w; if w = v, use u; else use u (or w)
  by_cases huv : u = v
  · use w
    refine ⟨Or.inl hw_A, ?_, ?_⟩
    · intro hwv; rw [huv, hwv] at huw; exact huw rfl
    · rw [Finset.mem_sym2_iff]; exact ⟨hv_T, hw_T, by intro h; rw [huv, h] at huw; exact huw rfl⟩
  · use u
    refine ⟨Or.inl hu_A, huv, ?_⟩
    rw [Finset.mem_sym2_iff]; exact ⟨hv_T, hu_T, huv⟩

end
