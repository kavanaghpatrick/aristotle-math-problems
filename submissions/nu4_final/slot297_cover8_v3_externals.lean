/-
  slot297: PATH_4 τ ≤ 8 - Focus on v3-external triangles

  SINGLE SORRY FOCUS: Prove v3_external_covered_by_cover8

  This is symmetric to slot296 but for v3 (the other endpoint).

  KEY INSIGHT:
  For v3-triangles t = {v3, x, y} where t ∉ M:
  - t shares edge with C or D (since v3 ∉ A, v3 ∉ B in PATH_4)
  - If t shares {v3,c}: covered by {v3,c}
  - If t shares {v2,v3}: covered by {v2,v3}
  - If t shares {v2,c}: need to show v2 ∈ t → covered
  - If t shares {v3,d1}: covered by {v3,d1}
  - If t shares {v3,d2}: this is the gap! cover8 doesn't have {v3,d2}
  - If t shares {d1,d2}: covered by {d1,d2}

  THE 8-EDGE COVER:
  E = {s(a1,a2), s(d1,d2), s(v1,v2), s(v2,v3), s(v1,a1), s(v1,b), s(v3,c), s(v3,d1)}

  GAP ANALYSIS for v3-triangles:
  - {v3,d2,x} where x ∉ {d1,v2,c}: shares edge {v3,d2} with D
  - cover8 has {d1,d2} and {v3,d1} but NOT {v3,d2}
  - Need to show either d1 ∈ t, or x ∈ {v2,c,d1}
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000

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

variable (G : SimpleGraph V) [DecidableRel G.Adj]

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

/-- The corrected 8-edge cover for PATH_4 -/
def cover8 (v1 v2 v3 a1 a2 b c d1 d2 : V) : Finset (Sym2 V) :=
  {s(a1, a2), s(d1, d2), s(v1, v2), s(v2, v3),
   s(v1, a1), s(v1, b), s(v3, c), s(v3, d1)}

/-!
### Key Helper: v3-externals must share edge with C or D

PROOF SKETCH:
1. t = {v3, x, y} is a triangle not in M
2. By maximality, t shares edge with some m ∈ M
3. Since v3 ∈ t and v3 ∉ A ∪ B, if t shares edge with A or B,
   then |t ∩ A| ≥ 2 or |t ∩ B| ≥ 2 with v3 ∉ A, v3 ∉ B
4. This means {x,y} ⊆ A or {x,y} ⊆ B
5. In this case, v3-triangle is covered by A-edges or B-edges
-/
lemma v3_external_structure (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hv3_not_A : v3 ∉ A) (hv3_not_B : v3 ∉ B)
    (ht : t ∈ G.cliqueFinset 3) (hv3_in : v3 ∈ t) (ht_not : t ∉ M) :
    (∃ m ∈ ({C, D} : Finset (Finset V)), (t ∩ m).card ≥ 2) ∨
    (∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ u ≠ v3 ∧ v ≠ v3 ∧ (u ∈ A ∨ u ∈ B) ∧ (v ∈ A ∨ v ∈ B)) := by
  obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_not
  rw [hM_eq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · -- t shares edge with A, but v3 ∉ A
    right
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    use x, y
    refine ⟨hx.1, hy.1, hxy, ?_, ?_, Or.inl hx.2, Or.inl hy.2⟩
    · intro hxv3; exact hv3_not_A (hxv3 ▸ hx.2)
    · intro hyv3; exact hv3_not_A (hyv3 ▸ hy.2)
  · -- t shares edge with B, but v3 ∉ B
    right
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    use x, y
    refine ⟨hx.1, hy.1, hxy, ?_, ?_, Or.inr hx.2, Or.inr hy.2⟩
    · intro hxv3; exact hv3_not_B (hxv3 ▸ hx.2)
    · intro hyv3; exact hv3_not_B (hyv3 ▸ hy.2)
  · left; use C; simp [h_share]
  · left; use D; simp [h_share]

/-!
### Main Theorem: v3-externals are covered by cover8

PROOF SKETCH:
1. By v3_external_structure, either t shares edge with C/D, or t has {x,y} ⊆ A ∪ B
2. Case t shares edge with C:
   - If shares {v2,v3}: covered by s(v2,v3)
   - If shares {v3,c}: covered by s(v3,c)
   - If shares {v2,c}: v3 ∉ {v2,c}, contradiction
3. Case t shares edge with D:
   - If shares {v3,d1}: covered by s(v3,d1)
   - If shares {v3,d2}: GAP - need to show d1 ∈ t
   - If shares {d1,d2}: covered by s(d1,d2)
4. Case {x,y} ⊆ A ∪ B: covered by A/B edges in cover8
-/
theorem v3_external_covered (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    -- Distinctness for PATH_4
    (hv12 : v1 ≠ v2) (hv23 : v2 ≠ v3) (hv13 : v1 ≠ v3)
    (ha1v1 : a1 ≠ v1) (ha2v1 : a2 ≠ v1) (ha12 : a1 ≠ a2)
    (hbv1 : b ≠ v1) (hbv2 : b ≠ v2)
    (hcv2 : c ≠ v2) (hcv3 : c ≠ v3)
    (hd1v3 : d1 ≠ v3) (hd2v3 : d2 ≠ v3) (hd12 : d1 ≠ d2)
    -- PATH_4 disjointness
    (hv3_not_A : v3 ∉ A) (hv3_not_B : v3 ∉ B)
    (hd1_not_C : d1 ∉ C) (hd2_not_C : d2 ∉ C)
    (ht : t ∈ G.cliqueFinset 3) (hv3_in : v3 ∈ t) (ht_not : t ∉ M) :
    ∃ e ∈ (cover8 v1 v2 v3 a1 a2 b c d1 d2).filter (fun e => e ∈ G.edgeFinset), e ∈ t.sym2 := by
  rcases v3_external_structure G M A B C D v1 v2 v3 a1 a2 b c d1 d2 t hM hM_eq hA_eq hB_eq hC_eq hD_eq
         hv3_not_A hv3_not_B ht hv3_in ht_not with h_CD | h_AB
  · -- Case: t shares edge with C or D
    obtain ⟨m, hm, h_share⟩ := h_CD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    rcases hm with rfl | rfl
    · -- m = C: t shares edge with C = {v2, v3, c}
      rw [hC_eq] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      by_cases hxv3 : x = v3
      · subst hxv3
        rcases hy.2 with rfl | rfl | rfl
        · exact absurd rfl hxy
        · -- y = v2, use edge {v2, v3}
          use s(v2, v3)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv2C : v2 ∈ C := by rw [hC_eq]; simp
            have hv3C : v3 ∈ C := by rw [hC_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv2C hv3C hv23)
          · rw [Sym2.eq_swap]; exact edge_in_triangle_sym2 t v3 v2 hv3_in hy.1
        · -- y = c, use edge {v3, c}
          use s(v3, c)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv3C : v3 ∈ C := by rw [hC_eq]; simp
            have hcC : c ∈ C := by rw [hC_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3C hcC hcv3.symm)
          · exact edge_in_triangle_sym2 t v3 c hv3_in hy.1
      · rcases hx.2 with rfl | rfl | rfl
        · exact absurd rfl hxv3
        · use s(v2, v3); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv2C : v2 ∈ C := by rw [hC_eq]; simp
            have hv3C : v3 ∈ C := by rw [hC_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv2C hv3C hv23)
          · rw [Sym2.eq_swap]; exact edge_in_triangle_sym2 t v3 v2 hv3_in hx.1
        · use s(v3, c); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv3C : v3 ∈ C := by rw [hC_eq]; simp
            have hcC : c ∈ C := by rw [hC_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3C hcC hcv3.symm)
          · exact edge_in_triangle_sym2 t v3 c hv3_in hx.1
    · -- m = D: t shares edge with D = {v3, d1, d2}
      rw [hD_eq] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      by_cases hxv3 : x = v3
      · subst hxv3
        rcases hy.2 with rfl | rfl | rfl
        · exact absurd rfl hxy
        · -- y = d1, use edge {v3, d1}
          use s(v3, d1)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv3D : v3 ∈ D := by rw [hD_eq]; simp
            have hd1D : d1 ∈ D := by rw [hD_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hD_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3D hd1D hd1v3.symm)
          · exact edge_in_triangle_sym2 t v3 d1 hv3_in hy.1
        · -- y = d2: GAP! cover8 doesn't have {v3, d2}
          -- Need to show d1 is also in t, or use {d1,d2}
          -- Key insight: t = {v3, d2, z} for some z
          -- If z = d1: covered by {v3, d1} or {d1, d2}
          -- If z ≠ d1: need to prove this can't happen
          sorry
      · rcases hx.2 with rfl | rfl | rfl
        · exact absurd rfl hxv3
        · use s(v3, d1); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv3D : v3 ∈ D := by rw [hD_eq]; simp
            have hd1D : d1 ∈ D := by rw [hD_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hD_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3D hd1D hd1v3.symm)
          · exact edge_in_triangle_sym2 t v3 d1 hv3_in hx.1
        · -- x = d2: same gap
          sorry
  · -- Case: {x,y} ⊆ A ∪ B
    -- t = {v3, x, y} where x, y ∈ A ∪ B
    -- A = {v1, a1, a2}, B = {v1, v2, b}
    -- If v1 ∈ {x,y}: use {v1,v2} or {v1,a1} or {v1,b}
    -- If v2 ∈ {x,y}: use {v1,v2} or {v2,v3}
    sorry

end
