/-
  slot295: Key Lemma - Triangles containing v1 have neighbor in cover

  SINGLE SORRY FOCUS: Prove v1_triangle_has_cover_neighbor

  INSIGHT: If t = {v1, x, y} is a triangle not in M, by maximality t shares
  an edge with some M-element. Since v1 ∈ t:
  - If t shares edge with A or B (which contain v1), then {x,y} ∩ (A ∪ B) ≠ ∅
  - If t shares edge with C or D (which don't contain v1), then {x,y} ⊆ C or {x,y} ⊆ D

  Cover10 edges at v1: {v1,a1}, {v1,a2}, {v1,v2}
  Cover10 edges not at v1: {a1,a2}, {v2,b}, {v2,v3}, {v3,c}, {d1,d2}, {v3,d1}, {v3,d2}

  For t = {v1,x,y} to be covered:
  - If x or y ∈ {a1,a2,v2}: covered by v1-incident edge
  - If {x,y} ⊆ C = {v2,v3,c}: covered by {v2,v3} or {v3,c}
  - If {x,y} ⊆ D = {v3,d1,d2}: covered by {v3,d1}, {v3,d2}, or {d1,d2}
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

/-- The 10-edge cover for PATH_4 -/
def cover10 (v1 v2 v3 a1 a2 b c d1 d2 : V) : Finset (Sym2 V) :=
  {s(a1, a2), s(v1, a1), s(v1, a2),
   s(v1, v2), s(v2, b),
   s(v2, v3), s(v3, c),
   s(d1, d2), s(v3, d1), s(v3, d2)}

/-!
### Main Lemma: v1-triangles are covered by cover10

PROOF SKETCH:
1. Let t = {v1, x, y} be a triangle with t ∉ M
2. By maximality, t shares edge with some m ∈ M = {A, B, C, D}
3. Case m = A: t ∩ A ⊇ 2, so {x,y} ∩ {a1,a2} ≠ ∅ → covered by {v1,a1} or {v1,a2}
4. Case m = B: t ∩ B ⊇ 2, so {x,y} ∩ {v2,b} ≠ ∅ → covered by {v1,v2} or need {v2,b}
5. Case m = C: t ∩ C ⊇ 2, v1 ∉ C, so {x,y} ⊆ C → covered by C-edges
6. Case m = D: t ∩ D ⊇ 2, v1 ∉ D, so {x,y} ⊆ D → covered by D-edges
-/
theorem v1_triangle_covered (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    (hv12 : v1 ≠ v2) (hv23 : v2 ≠ v3) (hv13 : v1 ≠ v3)
    (ha1v1 : a1 ≠ v1) (ha2v1 : a2 ≠ v1) (ha12 : a1 ≠ a2)
    (hd1v3 : d1 ≠ v3) (hd2v3 : d2 ≠ v3) (hd12 : d1 ≠ d2)
    -- PATH_4 disjointness
    (hv1_not_C : v1 ∉ C) (hv1_not_D : v1 ∉ D)
    (ht : t ∈ G.cliqueFinset 3) (hv1_in : v1 ∈ t) (ht_not : t ∉ M) :
    ∃ e ∈ (cover10 v1 v2 v3 a1 a2 b c d1 d2).filter (fun e => e ∈ G.edgeFinset), e ∈ t.sym2 := by
  -- By maximality, t shares edge with some M-element
  obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_not
  rw [hM_eq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  -- Get the two vertices in intersection
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
  simp only [Finset.mem_inter] at hx hy
  rcases hm with rfl | rfl | rfl | rfl
  · -- Case: t shares edge with A = {v1, a1, a2}
    -- Since v1 ∈ t and |t ∩ A| ≥ 2, at least one of a1, a2 is in t
    rw [hA_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    by_cases hxv1 : x = v1
    · subst hxv1
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · -- y = a1 ∈ t, use edge {v1, a1}
        use s(v1, a1)
        constructor
        · simp only [Finset.mem_filter, cover10, Finset.mem_insert, Finset.mem_singleton, true_or, true_and]
          have hv1A : v1 ∈ A := by rw [hA_eq]; simp
          have ha1A : a1 ∈ A := by rw [hA_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
        · exact edge_in_triangle_sym2 t v1 a1 hv1_in hy.1
      · -- y = a2 ∈ t, use edge {v1, a2}
        use s(v1, a2)
        constructor
        · simp only [Finset.mem_filter, cover10, Finset.mem_insert, Finset.mem_singleton, true_or, or_true, true_and]
          have hv1A : v1 ∈ A := by rw [hA_eq]; simp
          have ha2A : a2 ∈ A := by rw [hA_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha2A ha2v1.symm)
        · exact edge_in_triangle_sym2 t v1 a2 hv1_in hy.1
    · -- x ≠ v1, so x ∈ {a1, a2}
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · use s(v1, a1); constructor
        · simp only [Finset.mem_filter, cover10, Finset.mem_insert, Finset.mem_singleton, true_or, true_and]
          have hv1A : v1 ∈ A := by rw [hA_eq]; simp
          have ha1A : a1 ∈ A := by rw [hA_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
        · exact edge_in_triangle_sym2 t v1 a1 hv1_in hx.1
      · use s(v1, a2); constructor
        · simp only [Finset.mem_filter, cover10, Finset.mem_insert, Finset.mem_singleton, true_or, or_true, true_and]
          have hv1A : v1 ∈ A := by rw [hA_eq]; simp
          have ha2A : a2 ∈ A := by rw [hA_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha2A ha2v1.symm)
        · exact edge_in_triangle_sym2 t v1 a2 hv1_in hx.1
  · -- Case: t shares edge with B = {v1, v2, b}
    rw [hB_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    by_cases hxv1 : x = v1
    · subst hxv1
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · -- y = v2 ∈ t, use edge {v1, v2}
        use s(v1, v2)
        constructor
        · simp only [Finset.mem_filter, cover10, Finset.mem_insert, Finset.mem_singleton, true_or, or_true, true_and]
          have hv1B : v1 ∈ B := by rw [hB_eq]; simp
          have hv2B : v2 ∈ B := by rw [hB_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
        · exact edge_in_triangle_sym2 t v1 v2 hv1_in hy.1
      · -- y = b ∈ t. Need to cover {v1, b, z} for some z.
        -- This is the HARD CASE - cover10 doesn't have {v1, b}!
        -- We need {v2, b} to work, but that requires v2 ∈ t
        sorry
    · rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · use s(v1, v2); constructor
        · simp only [Finset.mem_filter, cover10, Finset.mem_insert, Finset.mem_singleton, true_or, or_true, true_and]
          have hv1B : v1 ∈ B := by rw [hB_eq]; simp
          have hv2B : v2 ∈ B := by rw [hB_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
        · exact edge_in_triangle_sym2 t v1 v2 hv1_in hx.1
      · -- x = b, same hard case
        sorry
  · -- Case: t shares edge with C = {v2, v3, c}
    -- v1 ∉ C, so t ∩ C ⊆ t \ {v1}
    -- Since |t ∩ C| ≥ 2 and t = {v1, z1, z2}, we need {z1, z2} ⊆ C
    -- So t = {v1, u, w} where {u, w} ⊆ {v2, v3, c}
    -- One of {v2,v3}, {v2,c}, {v3,c} covers t
    have ht3 : t.card = 3 := triangle_card_3 G t ht
    -- The intersection t ∩ C has at least 2 elements
    -- Since v1 ∉ C, these elements are from t \ {v1}
    have h_inter_sub : t ∩ C ⊆ t.erase v1 := by
      intro z hz
      simp only [Finset.mem_inter, Finset.mem_erase] at hz ⊢
      exact ⟨fun heq => hv1_not_C (heq ▸ hz.2), hz.1⟩
    -- t \ {v1} has at most 2 elements
    have h_erase_card : (t.erase v1).card = 2 := by
      rw [Finset.card_erase_of_mem hv1_in, ht3]
    -- So t ∩ C = t \ {v1} (both have 2 elements)
    have h_inter_eq : t ∩ C = t.erase v1 := by
      apply Finset.eq_of_subset_of_card_le h_inter_sub
      rw [h_erase_card]
      exact h_share
    -- Get the two elements of t \ {v1}
    rw [hC_eq] at h_inter_eq
    -- t.erase v1 ⊆ {v2, v3, c}, so t contains two of v2, v3, c
    -- Use one of the C-edges
    sorry
  · -- Case: t shares edge with D = {v3, d1, d2}
    -- Similar to C case
    sorry

end
