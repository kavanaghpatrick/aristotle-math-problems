/-
Tuza ν=4: τ ≤ 12 Reconfirmation (Slot 212)

GOAL: Reconfirm the τ ≤ 12 bound with simplified proof.

This is a BACKUP slot in case the τ ≤ 8 and τ ≤ 10 approaches fail.
The proof is intentionally simple and robust.

STRATEGY:
  - Use ALL 12 edges of the packing M = {A, B, C, D}
  - 4 triangles × 3 edges = 12 edges (with some sharing at intersections)
  - Every triangle shares edge with M (proven in slot139)
  - Therefore the 12 M-edges cover all triangles

This is essentially slot139 with explicit cardinality tracking.
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

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: Every triangle shares edge with packing
-- ══════════════════════════════════════════════════════════════════════════════

axiom triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING EDGES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Union of all edges from all packing elements -/
def allPackingEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun A => A.sym2)

/-- Packing edges are valid graph edges -/
lemma allPackingEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    allPackingEdges G M ⊆ G.edgeFinset := by
  intro e he
  simp only [allPackingEdges, Finset.mem_biUnion] at he
  obtain ⟨A, hA_M, he_A⟩ := he
  rw [Finset.mem_sym2_iff] at he_A
  obtain ⟨ha, hb, hab⟩ := he_A
  rw [SimpleGraph.mem_edgeFinset]
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1.1 hA_M
  have hA_is_clique := (SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).1
  exact hA_is_clique.2 ha hb hab

/-- Each M-element contributes at most 3 edges -/
lemma sym2_card_le_3 (A : Finset V) (hA : A.card = 3) : A.sym2.card = 3 := by
  rw [Finset.card_sym2, hA]
  native_decide

/-- All packing edges have cardinality ≤ 3 * |M| -/
lemma allPackingEdges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    (allPackingEdges G M).card ≤ 3 * M.card := by
  simp only [allPackingEdges]
  calc (M.biUnion (fun A => A.sym2)).card
      ≤ M.sum (fun A => A.sym2.card) := Finset.card_biUnion_le
    _ ≤ M.sum (fun _ => 3) := by
        apply Finset.sum_le_sum
        intro A hA
        have hA_clique : A ∈ G.cliqueFinset 3 := hM.1.1 hA
        have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).2
        rw [sym2_card_le_3 A hA_card]
    _ = 3 * M.card := by simp [Finset.sum_const, Finset.card_eq_sum_ones]

/-- All packing edges cover all triangles -/
lemma allPackingEdges_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ allPackingEdges G M, e ∈ t.sym2 := by
  intro t ht
  obtain ⟨X, hX_M, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- Extract two vertices from intersection
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hX_share
  have hu_t := (Finset.mem_inter.mp hu).1
  have hv_t := (Finset.mem_inter.mp hv).1
  have hu_X := (Finset.mem_inter.mp hu).2
  have hv_X := (Finset.mem_inter.mp hv).2
  use s(u, v)
  constructor
  · simp only [allPackingEdges, Finset.mem_biUnion]
    use X, hX_M
    rw [Finset.mem_sym2_iff]
    exact ⟨hu_X, hv_X, huv⟩
  · rw [Finset.mem_sym2_iff]
    exact ⟨hu_t, hv_t, huv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 12 for ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ ≤ 12 = 3 * 4 for ν = 4 -/
theorem tau_le_12_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumber G ≤ 12 := by
  let E := allPackingEdges G M
  have hE_sub := allPackingEdges_subset G M hM
  have hE_card : E.card ≤ 12 := by
    calc E.card ≤ 3 * M.card := allPackingEdges_card G M hM
       _ = 3 * 4 := by rw [hM_card]
       _ = 12 := by norm_num
  have hE_cover := allPackingEdges_cover G M hM
  have hE_valid : isTriangleCover G E := ⟨hE_sub, hE_cover⟩
  have hE_in : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hE_sub, hE_valid⟩

  unfold triangleCoveringNumber
  have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨E, hE_in⟩
  have h_in_image : E.card ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card :=
    Finset.mem_image_of_mem _ hE_in
  have h_min_le := Finset.min'_le _ E.card h_in_image
  calc (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0
    ≤ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min' (Finset.Nonempty.image h_nonempty _) := by
      simp only [Finset.min_eq_min']; rfl
    _ ≤ E.card := h_min_le
    _ ≤ 12 := hE_card

/-- General formulation: τ ≤ 3ν -/
theorem tau_le_3nu (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    triangleCoveringNumber G ≤ 3 * M.card := by
  let E := allPackingEdges G M
  have hE_sub := allPackingEdges_subset G M hM
  have hE_card := allPackingEdges_card G M hM
  have hE_cover := allPackingEdges_cover G M hM
  have hE_valid : isTriangleCover G E := ⟨hE_sub, hE_cover⟩
  have hE_in : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hE_sub, hE_valid⟩

  unfold triangleCoveringNumber
  have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨E, hE_in⟩
  have h_in_image : E.card ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card :=
    Finset.mem_image_of_mem _ hE_in
  have h_min_le := Finset.min'_le _ E.card h_in_image
  calc (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0
    ≤ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min' (Finset.Nonempty.image h_nonempty _) := by
      simp only [Finset.min_eq_min']; rfl
    _ ≤ E.card := h_min_le
    _ ≤ 3 * M.card := hE_card

end
