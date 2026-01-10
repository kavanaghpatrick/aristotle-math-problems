/-
  slot296: PATH_4 τ ≤ 8 - Focus on v1-external triangles

  SINGLE SORRY FOCUS: Prove v1_external_covered_by_cover8

  KEY INSIGHT from deep analysis:
  The correct 8-edge cover must include:
  - {a1,a2}, {d1,d2} (mandatory for base-privates)
  - {v1,v2}, {v2,v3} (mandatory for spine-shared triangles)
  - 4 more edges to cover remaining externals

  CRITICAL OBSERVATION:
  For v1-triangles t = {v1, x, y} where t ∉ M:
  - t shares edge with A or B (since v1 ∉ C, v1 ∉ D)
  - If t shares {v1,a1}: covered by {v1,a1}
  - If t shares {v1,a2}: covered by {v1,a2}
  - If t shares {a1,a2}: covered by {a1,a2}
  - If t shares {v1,v2}: covered by {v1,v2}
  - If t shares {v1,b}: must show b ∈ cover or b-edge

  THE 8-EDGE COVER:
  E = {s(a1,a2), s(d1,d2), s(v1,v2), s(v2,v3), s(v1,a1), s(v1,b), s(v3,c), s(v3,d1)}

  This covers:
  - All A-externals via {a1,a2} or {v1,a1}
  - All B-externals via {v1,v2} or {v1,b}
  - All C-externals via {v2,v3} or {v3,c}
  - All D-externals via {d1,d2} or {v3,d1}

  REMAINING GAPS to verify:
  - {v1,a2,x} where x ∉ {a1,v2,b}: NOT directly covered
  - {v3,d2,x} where x ∉ {d1,v2,c}: NOT directly covered

  LEMMA TO PROVE: Such triangles don't exist OR are covered by overlap
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

lemma cover8_card (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9) :
    (cover8 v1 v2 v3 a1 a2 b c d1 d2).card = 8 := by
  unfold cover8
  -- Need distinctness to show all 8 edges are different
  sorry

/-!
### Key Helper: v1-externals must share edge with A or B

PROOF SKETCH:
1. t = {v1, x, y} is a triangle not in M
2. By maximality, t shares edge with some m ∈ M
3. Since v1 ∈ t and v1 ∉ C ∪ D, if t shares edge with C or D,
   then |t ∩ C| ≥ 2 or |t ∩ D| ≥ 2 with v1 ∉ C, v1 ∉ D
4. This means {x,y} ⊆ C or {x,y} ⊆ D
5. But {x,y} ⊆ C means t shares edge {v2,v3}, {v2,c}, or {v3,c} with C
6. In this case, v1-triangle is actually a C-edge external, covered by {v2,v3} or {v3,c}
-/
lemma v1_external_structure (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hv1_not_C : v1 ∉ C) (hv1_not_D : v1 ∉ D)
    (ht : t ∈ G.cliqueFinset 3) (hv1_in : v1 ∈ t) (ht_not : t ∉ M) :
    -- t shares edge with A or B, OR t contains two vertices from C ∪ D
    (∃ m ∈ ({A, B} : Finset (Finset V)), (t ∩ m).card ≥ 2) ∨
    (∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ u ≠ v1 ∧ v ≠ v1 ∧ (u ∈ C ∨ u ∈ D) ∧ (v ∈ C ∨ v ∈ D)) := by
  obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_not
  rw [hM_eq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · left; use A; simp [h_share]
  · left; use B; simp [h_share]
  · -- t shares edge with C, but v1 ∉ C
    right
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    use x, y
    refine ⟨hx.1, hy.1, hxy, ?_, ?_, Or.inl hx.2, Or.inl hy.2⟩
    · intro hxv1; exact hv1_not_C (hxv1 ▸ hx.2)
    · intro hyv1; exact hv1_not_C (hyv1 ▸ hy.2)
  · -- t shares edge with D, but v1 ∉ D
    right
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    use x, y
    refine ⟨hx.1, hy.1, hxy, ?_, ?_, Or.inr hx.2, Or.inr hy.2⟩
    · intro hxv1; exact hv1_not_D (hxv1 ▸ hx.2)
    · intro hyv1; exact hv1_not_D (hyv1 ▸ hy.2)

/-!
### Main Theorem: v1-externals are covered by cover8

PROOF SKETCH:
1. By v1_external_structure, either t shares edge with A/B, or t has {x,y} ⊆ C ∪ D
2. Case t shares edge with A:
   - If shares {v1,a1}: covered by s(v1,a1)
   - If shares {v1,a2}: need to show covered (this is the gap!)
   - If shares {a1,a2}: covered by s(a1,a2)
3. Case t shares edge with B:
   - If shares {v1,v2}: covered by s(v1,v2)
   - If shares {v1,b}: covered by s(v1,b)
   - If shares {v2,b}: v1 ∉ {v2,b}, contradiction with v1 ∈ t
4. Case {x,y} ⊆ C ∪ D:
   - t = {v1, x, y} where x,y ∈ C ∪ D
   - One of {v2,v3}, {v3,c}, {v3,d1} covers {x,y}
-/
theorem v1_external_covered (M : Finset (Finset V)) (A B C D : Finset V)
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
    (hv1_not_C : v1 ∉ C) (hv1_not_D : v1 ∉ D)
    (ha1_not_B : a1 ∉ B) (ha2_not_B : a2 ∉ B)
    (ht : t ∈ G.cliqueFinset 3) (hv1_in : v1 ∈ t) (ht_not : t ∉ M) :
    ∃ e ∈ (cover8 v1 v2 v3 a1 a2 b c d1 d2).filter (fun e => e ∈ G.edgeFinset), e ∈ t.sym2 := by
  -- Use the structural lemma
  rcases v1_external_structure G M A B C D v1 v2 v3 a1 a2 b c d1 d2 t hM hM_eq hA_eq hB_eq hC_eq hD_eq
         hv1_not_C hv1_not_D ht hv1_in ht_not with h_AB | h_CD
  · -- Case: t shares edge with A or B
    obtain ⟨m, hm, h_share⟩ := h_AB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    rcases hm with rfl | rfl
    · -- m = A: t shares edge with A = {v1, a1, a2}
      rw [hA_eq] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      by_cases hxv1 : x = v1
      · subst hxv1
        rcases hy.2 with rfl | rfl | rfl
        · exact absurd rfl hxy
        · -- y = a1, use edge {v1, a1}
          use s(v1, a1)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv1A : v1 ∈ A := by rw [hA_eq]; simp
            have ha1A : a1 ∈ A := by rw [hA_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
          · exact edge_in_triangle_sym2 t v1 a1 hv1_in hy.1
        · -- y = a2: cover8 doesn't have {v1,a2}!
          -- KEY INSIGHT: {v1,a2} triangles are covered by {a1,a2} if a1 ∈ t
          -- We need to show that either:
          -- 1. a1 ∈ t (then {a1,a2} covers), OR
          -- 2. t shares another edge (with B) that IS in cover8
          sorry
      · rcases hx.2 with rfl | rfl | rfl
        · exact absurd rfl hxv1
        · use s(v1, a1); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv1A : v1 ∈ A := by rw [hA_eq]; simp
            have ha1A : a1 ∈ A := by rw [hA_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
          · exact edge_in_triangle_sym2 t v1 a1 hv1_in hx.1
        · -- x = a2, same issue
          sorry
    · -- m = B: t shares edge with B = {v1, v2, b}
      rw [hB_eq] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      by_cases hxv1 : x = v1
      · subst hxv1
        rcases hy.2 with rfl | rfl | rfl
        · exact absurd rfl hxy
        · use s(v1, v2); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv1B : v1 ∈ B := by rw [hB_eq]; simp
            have hv2B : v2 ∈ B := by rw [hB_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
          · exact edge_in_triangle_sym2 t v1 v2 hv1_in hy.1
        · -- y = b, use edge {v1, b}
          use s(v1, b); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv1B : v1 ∈ B := by rw [hB_eq]; simp
            have hbB : b ∈ B := by rw [hB_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hbB hbv1.symm)
          · exact edge_in_triangle_sym2 t v1 b hv1_in hy.1
      · rcases hx.2 with rfl | rfl | rfl
        · exact absurd rfl hxv1
        · use s(v1, v2); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv1B : v1 ∈ B := by rw [hB_eq]; simp
            have hv2B : v2 ∈ B := by rw [hB_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
          · exact edge_in_triangle_sym2 t v1 v2 hv1_in hx.1
        · use s(v1, b); constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hv1B : v1 ∈ B := by rw [hB_eq]; simp
            have hbB : b ∈ B := by rw [hB_eq]; simp
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hbB hbv1.symm)
          · exact edge_in_triangle_sym2 t v1 b hv1_in hx.1
  · -- Case: t = {v1, x, y} where {x, y} ⊆ C ∪ D
    obtain ⟨u, v, hu_t, hv_t, huv, hu_ne_v1, hv_ne_v1, hu_CD, hv_CD⟩ := h_CD
    -- t = {v1, u, v} where u, v ∈ C ∪ D
    -- cover8 has {v2,v3}, {v3,c}, {v3,d1} which should cover {u,v}
    -- Need case analysis on whether u,v are in C, D, or both
    sorry

end
