/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bd79807a-f08b-4a01-b406-c467b05618b6
-/

/-
  slot290: PATH_4 τ ≤ 12 - Fixed DecidablePred issue

  DATE: Jan 7, 2026

  FIX: Add `open Classical` to make predicates decidable
-/

import Mathlib


set_option linter.mathlibStandardSet false

set_option maxHeartbeats 400000

set_option maxRecDepth 4000

open Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isPath4Config (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (A B C D : Finset V) (v1 v2 v3 : V) : Prop :=
  M = {A, B, C, D} ∧
  A ∈ G.cliqueFinset 3 ∧ B ∈ G.cliqueFinset 3 ∧ C ∈ G.cliqueFinset 3 ∧ D ∈ G.cliqueFinset 3 ∧
  A ∩ B = {v1} ∧ B ∩ C = {v2} ∧ C ∩ D = {v3} ∧
  A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ D = ∅ ∧
  v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3

variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- PROVEN lemmas
lemma triangle_card_3 (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 := by
  simp only [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff, Finset.mem_filter] at ht
  exact ht.2

lemma edge_in_triangle_sym2 (t : Finset V) (u w : V) (hu : u ∈ t) (hw : w ∈ t) :
    s(u, w) ∈ t.sym2 := by
  simp only [Finset.mem_sym2_iff]
  exact ⟨hu, hw⟩

lemma max_packing_shares_edge (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not : t ∉ M) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  by_contra h
  push_neg at h
  have h_packing : isTrianglePacking G (insert t M) := by
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM.1.1 hx
    · intro x hx y hy hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact Nat.lt_succ_iff.mp (h y hy)
      · rw [Finset.inter_comm]; exact Nat.lt_succ_iff.mp (h x hx)
      · exact hM.1.2 hx hy hxy
  have h_card : (insert t M).card = M.card + 1 := Finset.card_insert_of_not_mem ht_not
  have h_le : (insert t M).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : insert t M ∈ (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_img := Finset.mem_image_of_mem Finset.card h_mem
    exact Finset.le_max h_img |> WithTop.coe_le_coe.mp
  omega

lemma triangle_sym2_card_le_3 (t : Finset V) (ht : t.card = 3) : t.sym2.card ≤ 3 := by
  have h : t.sym2.card = t.card.choose 2 := Finset.card_sym2 t
  simp [ht, Nat.choose] at h
  omega

def packingEdges (A B C D : Finset V) : Finset (Sym2 V) :=
  (A.sym2 ∪ B.sym2 ∪ C.sym2 ∪ D.sym2).filter (fun e => e ∈ G.edgeFinset)

lemma packingEdges_subset (A B C D : Finset V) :
    packingEdges G A B C D ⊆ G.edgeFinset := by
  unfold packingEdges
  intro e he
  simp only [Finset.mem_filter] at he
  exact he.2

/-! ### Main Theorem -/

theorem tau_le_12_path4 (M : Finset (Finset V)) (A B C D : Finset V) (v1 v2 v3 : V)
    (hM : isMaxPacking G M)
    (hPath : isPath4Config G M A B C D v1 v2 v3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 12 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use packingEdges G A B C D
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 12
    unfold packingEdges
    have hA3 : A.card = 3 := triangle_card_3 G A hPath.2.1.1
    have hB3 : B.card = 3 := triangle_card_3 G B hPath.2.1.2.1
    have hC3 : C.card = 3 := triangle_card_3 G C hPath.2.1.2.2.1
    have hD3 : D.card = 3 := triangle_card_3 G D hPath.2.1.2.2.2
    have hAsym : A.sym2.card ≤ 3 := triangle_sym2_card_le_3 A hA3
    have hBsym : B.sym2.card ≤ 3 := triangle_sym2_card_le_3 B hB3
    have hCsym : C.sym2.card ≤ 3 := triangle_sym2_card_le_3 C hC3
    have hDsym : D.sym2.card ≤ 3 := triangle_sym2_card_le_3 D hD3
    calc ((A.sym2 ∪ B.sym2 ∪ C.sym2 ∪ D.sym2).filter (fun e => e ∈ G.edgeFinset)).card
        ≤ (A.sym2 ∪ B.sym2 ∪ C.sym2 ∪ D.sym2).card := Finset.card_filter_le _ _
      _ ≤ A.sym2.card + B.sym2.card + C.sym2.card + D.sym2.card := by
          calc (A.sym2 ∪ B.sym2 ∪ C.sym2 ∪ D.sym2).card
              ≤ (A.sym2 ∪ B.sym2 ∪ C.sym2).card + D.sym2.card := Finset.card_union_le _ _
            _ ≤ (A.sym2 ∪ B.sym2).card + C.sym2.card + D.sym2.card := by
                have := Finset.card_union_le (A.sym2 ∪ B.sym2) C.sym2
                omega
            _ ≤ A.sym2.card + B.sym2.card + C.sym2.card + D.sym2.card := by
                have := Finset.card_union_le A.sym2 B.sym2
                omega
      _ ≤ 3 + 3 + 3 + 3 := by omega
      _ = 12 := by norm_num
  · exact packingEdges_subset G A B C D
  · intro t ht
    by_cases ht_in : t ∈ M
    · rw [hPath.1] at ht_in
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
      rcases ht_in with rfl | rfl | rfl | rfl
      all_goals {
        have h3 : t.card = 3 := triangle_card_3 G t (by assumption)
        have hne : t.sym2.Nonempty := by rw [Finset.sym2_nonempty]; omega
        obtain ⟨e, he⟩ := hne
        use e
        constructor
        · unfold packingEdges
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · simp only [he, or_true, true_or]
          · have hclique := SimpleGraph.mem_cliqueFinset_iff.mp (by assumption)
            simp only [Finset.mem_sym2_iff] at he
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 he.1 he.2 (by
              intro heq
              have := Finset.card_sym2 t
              simp [h3, Nat.choose] at this
              rw [heq] at he
              simp at he
              omega))
        · exact he
      }
    · obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_in
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
      simp only [Finset.mem_inter] at hx hy
      use s(x, y)
      constructor
      · unfold packingEdges
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rw [hPath.1] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl
          all_goals simp only [Finset.mem_sym2_iff, hx.2, hy.2, and_self, or_true, true_or]
        · have hclique := SimpleGraph.mem_cliqueFinset_iff.mp ht
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hx.1 hy.1 hxy)
      · exact edge_in_triangle_sym2 t x y hx.1 hy.1

end