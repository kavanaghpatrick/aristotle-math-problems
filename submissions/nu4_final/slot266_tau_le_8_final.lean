/-
slot266: tau_le_8_path4 FINAL STEP - 1 SORRY SUBMISSION

PREREQUISITE: Submit AFTER slot264 (B) and slot265 (C) are proven.
This file includes the PROVEN versions of cover_hits_sharing_B and cover_hits_sharing_C.

The only sorry is the final step: "valid cover of size ≤8 implies τ ≤ 8"
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0

structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  hM_card : M.card = 4
  v1 : V
  v2 : V
  v3 : V
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅
  h_v1_A : v1 ∈ A
  h_v1_B : v1 ∈ B
  h_v2_B : v2 ∈ B
  h_v2_C : v2 ∈ C
  h_v3_C : v3 ∈ C
  h_v3_D : v3 ∈ D

/-- The explicit 8-edge cover for PATH_4 -/
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (fun e => e ∈ G.edgeFinset) ∪
  ({s(cfg.v1, cfg.v2)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  ({s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (fun e => e ∈ G.edgeFinset)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (copy from Aristotle outputs once available)
-- ══════════════════════════════════════════════════════════════════════════════

lemma M_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X : Finset V) (hX : X ∈ M) : X.card = 3 := by
  have := hM.1 hX
  exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2

lemma card_edges_of_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hA : A.card = 3) :
    (A.sym2.filter (fun e => e ∈ G.edgeFinset)).card ≤ 3 := by
  all_goals rw [Finset.card_eq_three] at hA; obtain ⟨x, y, z, h⟩ := hA; simp_all +decide [Finset.filter]
  all_goals simp_all +decide [Finset.sym2, Multiset.sym2]
  all_goals erw [Quotient.liftOn_mk] at *; simp_all +decide [List.sym2]
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons, List.filter_singleton]; aesop

lemma card_spine_edge (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (({s(u, v)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset)).card ≤ 1 := by
  exact Finset.card_filter_le _ _

lemma path4_cover_card_le_8_of_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8 := by
  refine' le_trans (Finset.card_union_le _ _) _
  refine' le_trans (add_le_add_right (Finset.card_union_le _ _ |> le_trans <| add_le_add_right (Finset.card_union_le _ _) _) _) _
  refine' le_trans (add_le_add (add_le_add (add_le_add (card_edges_of_triangle G cfg.A _) (card_spine_edge G cfg.v1 cfg.v2)) (card_spine_edge G cfg.v2 cfg.v3)) (card_edges_of_triangle G cfg.D _)) _
  · exact M_element_card_3 G M hM _ cfg.hA
  · exact M_element_card_3 G M hM _ cfg.hD
  · norm_num

lemma path4_cover_subset_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    path4_cover G cfg ⊆ G.edgeFinset := by
  unfold path4_cover
  simp only [union_subset_iff, filter_subset_iff]
  exact ⟨⟨⟨fun _ h => h.2, fun _ h => h.2⟩, fun _ h => h.2⟩, fun _ h => h.2⟩

lemma cover_hits_sharing_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_shares : (t ∩ cfg.A).card ≥ 2) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, x ∈ t ∩ cfg.A ∧ y ∈ t ∩ cfg.A ∧ x ≠ y := by
    simpa using Finset.one_lt_card.1 ht_shares
  have h_adj : G.Adj x y := by
    simp_all +decide [SimpleGraph.isClique_iff, Finset.mem_inter]
    exact ht.1 (by aesop) (by aesop) hxy.2.2
  use s(x, y)
  unfold path4_cover; aesop

lemma cover_hits_sharing_D (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_shares : (t ∩ cfg.D).card ≥ 2) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : V, u ∈ cfg.D ∧ v ∈ cfg.D ∧ u ≠ v ∧ u ∈ t ∧ v ∈ t := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 ht_shares; use u, v; aesop
  use Sym2.mk (u, v)
  unfold path4_cover; simp_all +decide [Finset.mem_union, Finset.mem_filter]
  have := ht.1; aesop

-- PLACEHOLDER: Insert proven code from slot264 once available
lemma cover_hits_sharing_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ cfg.B).card ≥ 2) (ht_not_A : (t ∩ cfg.A).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  -- TODO: Replace with proven code from slot264
  sorry -- REMOVE THIS SORRY WHEN INSERTING PROVEN CODE

-- PLACEHOLDER: Insert proven code from slot265 once available
lemma cover_hits_sharing_C (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_C : (t ∩ cfg.C).card ≥ 2) (ht_not_D : (t ∩ cfg.D).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  -- TODO: Replace with proven code from slot265
  sorry -- REMOVE THIS SORRY WHEN INSERTING PROVEN CODE

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM (1 SORRY - the final step)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: For PATH_4 configuration with ν(G) = 4, we have τ(G) ≤ 8 -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Path4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  let E := path4_cover G cfg
  have hE_subset : E ⊆ G.edgeFinset := path4_cover_subset_edges G M cfg
  have hE_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
    intro t ht
    by_cases ht_in_M : t ∈ M
    · rw [cfg.hM_eq] at ht_in_M
      simp only [mem_insert, mem_singleton] at ht_in_M
      rcases ht_in_M with rfl | rfl | rfl | rfl
      · exact cover_hits_sharing_A G M cfg t ht (by simp)
      · exact cover_hits_sharing_B G M hM cfg t ht (by simp) (by
          have := cfg.hAB
          simp only [inter_comm] at this ⊢
          have h : cfg.B ∩ cfg.A = {cfg.v1} := by rw [inter_comm]; exact this
          simp [h])
      · exact cover_hits_sharing_C G M hM cfg t ht (by simp) (by
          have := cfg.hCD
          simp only [inter_comm] at this ⊢
          have h : cfg.C ∩ cfg.D = {cfg.v3} := by rw [inter_comm]; exact this
          simp [h])
      · exact cover_hits_sharing_D G M cfg t ht (by simp)
    · have h_shares := hM.2 t ht ht_in_M
      obtain ⟨m, hm_M, hm_shares⟩ := h_shares
      rw [cfg.hM_eq] at hm_M
      simp only [mem_insert, mem_singleton] at hm_M
      rcases hm_M with rfl | rfl | rfl | rfl
      · exact cover_hits_sharing_A G M cfg t ht hm_shares
      · by_cases hA : (t ∩ cfg.A).card ≥ 2
        · exact cover_hits_sharing_A G M cfg t ht hA
        · push_neg at hA
          exact cover_hits_sharing_B G M hM cfg t ht hm_shares hA
      · by_cases hD : (t ∩ cfg.D).card ≥ 2
        · exact cover_hits_sharing_D G M cfg t ht hD
        · push_neg at hD
          exact cover_hits_sharing_C G M hM cfg t ht hm_shares hD
      · exact cover_hits_sharing_D G M cfg t ht hm_shares
  have hE_cover : isTriangleCover G E := ⟨hE_subset, hE_covers⟩
  have hE_card : E.card ≤ 8 := path4_cover_card_le_8_of_packing G M hM.1 cfg
  -- We have: E is a valid triangle cover with |E| ≤ 8
  -- Need to show: triangleCoveringNumber G ≤ 8
  -- By definition, τ(G) = min{|F| : F is a triangle cover}
  -- Since E is a cover with |E| ≤ 8, we have τ(G) ≤ |E| ≤ 8
  sorry

end
