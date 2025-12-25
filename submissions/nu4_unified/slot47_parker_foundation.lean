/-
Tuza ν=4 Strategy - Slot 47: Parker Foundation Lemmas

GOAL: Prove parker_nu_le_2: τ ≤ 4 when ν ≤ 2

This is a foundational lemma for the partition cases.
When the packing splits into vertex-disjoint groups A and B with |A|+|B|=4,
we apply Parker bounds to each group.

APPROACH:
1. If ν = 1: Any two triangles share an edge (otherwise ν ≥ 2)
   - By Helly-type argument, all triangles share a common edge
   - τ ≤ 1 (one edge covers all)
   - Actually τ ≤ 2 (Parker's original bound)

2. If ν = 2: Let M = {t1, t2} be max packing
   - If t1 ∩ t2 = ∅ (vertex disjoint): τ ≤ 2 + 2 = 4
   - If |t1 ∩ t2| = 1 (share vertex): τ ≤ 4 (by tau_pair_le_4)
   - |t1 ∩ t2| ≥ 2 would mean they share edge, contradicting packing

PROVEN LEMMAS TO USE:
- intersecting_triangles_structure (from slot30)
- tau_pair_le_4 (once proven)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PARKER BOUND ν = 1: τ ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/--
When ν = 1, any two triangles share at least 2 vertices (an edge).
Otherwise we could form a packing of size 2.
-/
lemma packing_one_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3) :
    (t1 ∩ t2).card ≥ 2 := by
  by_contra h_small
  push_neg at h_small
  -- If (t1 ∩ t2).card ≤ 1, then {t1, t2} is a packing of size ≥ 2
  have h_packing : isTrianglePacking G {t1, t2} := by
    constructor
    · -- {t1, t2} ⊆ cliqueFinset 3
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      cases ht with
      | inl h => rw [h]; exact ht1
      | inr h => rw [h]; exact ht2
    · -- Pairwise edge-disjoint
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      cases ha with
      | inl ha =>
        cases hb with
        | inl hb => exact absurd (hb.symm.trans ha) hab
        | inr hb => rw [ha, hb]; exact h_small
      | inr ha =>
        cases hb with
        | inl hb => rw [ha, hb, Finset.inter_comm]; exact h_small
        | inr hb => exact absurd (hb.symm.trans ha) hab
  -- This contradicts ν = 1
  have h_card : ({t1, t2} : Finset (Finset V)).card ≥ 2 := by
    by_cases h_eq : t1 = t2
    · -- If t1 = t2, then (t1 ∩ t2).card = 3 ≥ 2, contradiction
      rw [h_eq] at h_small
      have h_self : (t2 ∩ t2).card = t2.card := by simp
      rw [SimpleGraph.mem_cliqueFinset_iff] at ht2
      rw [h_self, ht2.card_eq] at h_small
      linarith
    · simp [h_eq]
  -- ν ≥ 2, contradiction
  unfold trianglePackingNumber at h_nu
  have h_in : {t1, t2} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      cases ht with
      | inl h => rw [h]; exact ht1
      | inr h => rw [h]; exact ht2
    · exact h_packing
  have h_max : ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max ≥ 2 := by
    have h_card_in : ({t1, t2} : Finset (Finset V)).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card := by
      exact Finset.mem_image_of_mem _ h_in
    have h_ge : ({t1, t2} : Finset (Finset V)).card ≥ 2 := h_card
    calc ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max
        ≥ ({t1, t2} : Finset (Finset V)).card := Finset.le_max h_card_in
      _ ≥ 2 := h_ge
  simp only [h_nu, ge_iff_le] at h_max
  cases h : ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max with
  | none => simp [h] at h_nu
  | some m =>
    simp only [h, Option.getD_some] at h_nu
    rw [h] at h_max
    simp at h_max
    linarith

/--
When all triangles pairwise share edges, there exists a common edge.
Helly-type lemma for triangles.
-/
lemma all_share_edge_common_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_share : ∀ t1 t2 : Finset V, t1 ∈ G.cliqueFinset 3 → t2 ∈ G.cliqueFinset 3 → (t1 ∩ t2).card ≥ 2) :
    (G.cliqueFinset 3).Nonempty →
    ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ G.cliqueFinset 3, e ⊆ t := by
  intro h_nonempty
  -- By Helly's theorem for dimension 1 (edges)
  -- If every pair of triangles shares an edge, all triangles share a common edge
  -- This is because: take any 3 triangles t1, t2, t3
  -- e12 = common edge of t1, t2
  -- e13 = common edge of t1, t3
  -- e23 = common edge of t2, t3
  -- t1 has edges e12 and e13, both 2-subsets of a 3-set
  -- If e12 ≠ e13, they share exactly 1 vertex
  -- Similar reasoning gives: all eij share a common vertex v
  -- Then the common edge must pass through v
  sorry

/--
Parker's bound for ν = 1: τ ≤ 2
-/
lemma parker_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) :
    triangleCoveringNumber G ≤ 2 := by
  by_cases h_empty : (G.cliqueFinset 3).Nonempty
  · -- There are triangles
    have h_share := packing_one_implies_intersect G h_nu
    -- All pairs share an edge → common edge exists
    have h_common := all_share_edge_common_edge G (fun t1 t2 ht1 ht2 => h_share t1 t2 ht1 ht2) h_empty
    obtain ⟨e, he_card, he_sub⟩ := h_common
    -- The common edge covers all triangles
    -- τ ≤ 1 (actually), but we claim τ ≤ 2
    sorry
  · -- No triangles: τ = 0
    simp only [Finset.not_nonempty_iff_eq_empty] at h_empty
    unfold triangleCoveringNumber
    simp only [h_empty, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true_of_mem]
    simp only [Finset.mem_powerset]
    -- Empty set covers no triangles
    have h_in : (∅ : Finset (Sym2 V)) ∈ G.edgeFinset.powerset := Finset.empty_mem_powerset _
    have h_zero : (∅ : Finset (Sym2 V)).card = 0 := Finset.card_empty
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- PARKER BOUND ν ≤ 2: τ ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
Parker's bound for ν ≤ 2: τ ≤ 4

Case analysis:
- ν = 0: No triangles, τ = 0
- ν = 1: τ ≤ 2 (by parker_nu_1)
- ν = 2: Let M = {t1, t2}
  - If vertex disjoint: τ ≤ 2 + 2 = 4 (2 edges per triangle)
  - If share vertex: τ ≤ 4 (by tau_pair_le_4, once proven)
-/
lemma parker_nu_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card ≤ 2) :
    triangleCoveringNumber G ≤ 4 := by
  interval_cases M.card
  · -- M.card = 0: No triangles in packing
    -- If ν = 0, then no triangles exist (otherwise packing would be nonempty)
    have h_nu : trianglePackingNumber G = 0 := by
      rw [← hM.2]; simp
    -- τ = 0
    sorry
  · -- M.card = 1: ν = 1
    have h_nu : trianglePackingNumber G = 1 := by
      rw [← hM.2]; simp
    calc triangleCoveringNumber G ≤ 2 := parker_nu_1 G h_nu
      _ ≤ 4 := by linarith
  · -- M.card = 2: ν = 2
    -- Get the two elements
    obtain ⟨t1, t2, ht1, ht2, h_ne, h_eq⟩ : ∃ t1 t2, t1 ∈ M ∧ t2 ∈ M ∧ t1 ≠ t2 ∧ M = {t1, t2} := by
      have h_card : M.card = 2 := rfl
      obtain ⟨t1, t2, h_ne, h_eq⟩ := Finset.card_eq_two.mp h_card
      exact ⟨t1, t2, by rw [h_eq]; simp, by rw [h_eq]; simp, h_ne, h_eq⟩
    -- Packing property: (t1 ∩ t2).card ≤ 1
    have h_inter : (t1 ∩ t2).card ≤ 1 := by
      have := hM.1.2
      exact this ht1 ht2 h_ne
    -- Case split on intersection
    interval_cases (t1 ∩ t2).card
    · -- Vertex disjoint: (t1 ∩ t2).card = 0
      -- Each triangle needs ≤ 2 edges to cover its neighborhood
      -- Actually τ ≤ 3 + 3 = 6 naively, but τ ≤ 2 + 2 = 4 using structure
      sorry
    · -- Share one vertex: (t1 ∩ t2).card = 1
      -- Apply tau_pair_le_4
      sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX PARTITION THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

def vertexSetOf (S : Finset (Finset V)) : Finset V :=
  S.biUnion id

def triangleUnionOf (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Finset (Finset V) :=
  S.biUnion (trianglesSharingEdge G)

/--
When packing M splits into vertex-disjoint groups A and B,
τ(G) ≤ τ(triangles of A) + τ(triangles of B)
-/
lemma tau_vertex_partition_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤
      triangleCoveringNumberOn G (triangleUnionOf G A) +
      triangleCoveringNumberOn G (triangleUnionOf G B) := by
  -- Vertex disjoint means triangle neighborhoods are disjoint
  -- τ(G) = τ(all triangles) = τ(A-triangles ∪ B-triangles) ≤ τ(A) + τ(B)
  sorry

/--
For vertex-disjoint partition with |A| + |B| = 4:
τ ≤ 2|A| + 2|B| = 8
-/
theorem tau_le_8_vertex_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8 := by
  -- |A| + |B| = 4
  have h_sum : A.card + B.card = 4 := by
    rw [← hM_card, ← hAB]
    exact Finset.card_union_of_disjoint hAB_disj
  -- τ(A) ≤ 2|A| by Parker (restricted to A's subgraph)
  -- τ(B) ≤ 2|B| by Parker (restricted to B's subgraph)
  -- Total: τ ≤ 2|A| + 2|B| = 8
  sorry

-- Corollary for 2+2 split
theorem tau_le_8_vertex_partition_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_card : A.card = 2) (hB_card : B.card = 2)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8 := by
  apply tau_le_8_vertex_partition G M hM hM_card A B hAB hAB_disj
  · exact Finset.card_pos.mp (by rw [hA_card]; norm_num)
  · exact Finset.card_pos.mp (by rw [hB_card]; norm_num)
  · exact h_vertex_disj

end
