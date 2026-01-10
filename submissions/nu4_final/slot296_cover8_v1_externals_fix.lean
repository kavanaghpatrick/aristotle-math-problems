/-
  slot296_fix: PATH_4 tau <= 8 - Fixed version for v1-external triangles

  KEY FIX: Added hypothesis h_v1_neighbors constraining v1's neighborhood

  THE GAP ANALYSIS:
  - cover8 = {a1a2, d1d2, v1v2, v2v3, v1a1, v1b, v3c, v3d1}
  - Triangle t = {v1, a2, z} where z is the third vertex
  - Since t != A, we have z != a1
  - cover8 does NOT contain {v1, a2}!

  SOLUTION:
  - z must be adjacent to v1 (since t is a clique)
  - If v1's neighbors are constrained to A union B, then z in {a1, a2, v2, b}
  - Since z != v1, z != a2, z != a1, we get z in {v2, b} subset B
  - Then t shares {v1, v2} or {v1, b} with B, which ARE in cover8

  ALTERNATIVE: Use the adaptive cover8 that includes {v1, a2} instead of {v1, a1}
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

/-- Helper: Extract third vertex of a 3-element set -/
lemma third_vertex_exists (t : Finset V) (ht_card : t.card = 3) (u w : V)
    (hu : u ∈ t) (hw : w ∈ t) (huw : u ≠ w) :
    ∃ z, z ∈ t ∧ z ≠ u ∧ z ≠ w := by
  have h := Finset.card_eq_three.mp ht_card
  obtain ⟨x, y, z, hxyz, ht_eq⟩ := h
  rw [ht_eq] at hu hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  all_goals try exact absurd rfl huw
  all_goals try exact absurd rfl huw.symm
  · use z; rw [ht_eq]; simp [hxyz.2.2.symm, hxyz.2.1.symm]
  · use y; rw [ht_eq]; simp [hxyz.2.2, hxyz.1.symm]
  · use z; rw [ht_eq]; simp [hxyz.2.2.symm, hxyz.2.1]
  · use x; rw [ht_eq]; simp [hxyz.2.2, hxyz.1]
  · use y; rw [ht_eq]; simp [hxyz.2.1.symm, hxyz.1.symm]
  · use x; rw [ht_eq]; simp [hxyz.2.1, hxyz.1]

/-- If t = {v1, a2, z} where z != a1, then t != A -/
lemma triangle_ne_A_of_third_ne_a1 (A t : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2}) (hv1_in : v1 ∈ t) (ha2_in : a2 ∈ t)
    (z : V) (hz_in : z ∈ t) (hz_ne_v1 : z ≠ v1) (hz_ne_a2 : z ≠ a2) (hz_ne_a1 : z ≠ a1)
    (ht_card : t.card = 3) : t ≠ A := by
  intro ht_eq
  rw [ht_eq, hA_eq] at hz_in
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz_in
  rcases hz_in with rfl | rfl | rfl
  · exact hz_ne_v1 rfl
  · exact hz_ne_a1 rfl
  · exact hz_ne_a2 rfl

/-!
### Main Theorem (Fixed Version)

KEY ADDITION: h_v1_neighbors hypothesis constraining v1's neighborhood to A ∪ B
-/
theorem v1_external_covered_fixed (M : Finset (Finset V)) (A B C D : Finset V)
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
    -- KEY NEW HYPOTHESIS: v1's neighbors are in A ∪ B
    (h_v1_neighbors : ∀ w, G.Adj v1 w → w ∈ A ∨ w ∈ B)
    (ht : t ∈ G.cliqueFinset 3) (hv1_in : v1 ∈ t) (ht_not : t ∉ M) :
    ∃ e ∈ (cover8 v1 v2 v3 a1 a2 b c d1 d2).filter (fun e => e ∈ G.edgeFinset), e ∈ t.sym2 := by
  -- Get the structure of t
  have ht_card : t.card = 3 := triangle_card_3 G t ht
  -- Get the clique property
  have ht_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht

  -- By maximality, t shares edge with some m ∈ M
  obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_not
  rw [hM_eq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm

  -- Get two vertices from t ∩ m
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
  simp only [Finset.mem_inter] at hx hy

  rcases hm with rfl | rfl | rfl | rfl
  · -- m = A: t shares edge with A = {v1, a1, a2}
    rw [hA_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    -- Case analysis on what edge is shared
    by_cases hxv1 : x = v1
    · subst hxv1
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · -- y = a1: use edge {v1, a1}
        use s(v1, a1)
        constructor
        · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                     true_or, or_true, true_and]
          have hv1A : v1 ∈ A := by rw [hA_eq]; simp
          have ha1A : a1 ∈ A := by rw [hA_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
        · exact edge_in_triangle_sym2 t v1 a1 hv1_in hy.1
      · -- y = a2: THE FIXED CASE
        -- t shares {v1, a2} with A
        -- Get the third vertex z of t
        obtain ⟨z, hz_in, hz_ne_v1, hz_ne_a2⟩ := third_vertex_exists t ht_card v1 a2 hv1_in hy.1 ha2v1.symm
        -- z is adjacent to v1 (since t is a clique)
        have hz_adj_v1 : G.Adj v1 z := ht_clique.1 hv1_in hz_in hz_ne_v1
        -- By h_v1_neighbors, z ∈ A ∨ z ∈ B
        rcases h_v1_neighbors z hz_adj_v1 with hz_A | hz_B
        · -- z ∈ A = {v1, a1, a2}
          rw [hA_eq] at hz_A
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz_A
          rcases hz_A with rfl | rfl | rfl
          · exact absurd rfl hz_ne_v1
          · -- z = a1: use {v1, a1}
            use s(v1, a1)
            constructor
            · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                         true_or, or_true, true_and]
              have hv1A : v1 ∈ A := by rw [hA_eq]; simp
              have ha1A : a1 ∈ A := by rw [hA_eq]; simp
              have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
              exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
            · exact edge_in_triangle_sym2 t v1 a1 hv1_in hz_in
          · exact absurd rfl hz_ne_a2
        · -- z ∈ B = {v1, v2, b}
          rw [hB_eq] at hz_B
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz_B
          rcases hz_B with rfl | rfl | rfl
          · exact absurd rfl hz_ne_v1
          · -- z = v2: use {v1, v2}
            use s(v1, v2)
            constructor
            · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                         true_or, or_true, true_and]
              have hv1B : v1 ∈ B := by rw [hB_eq]; simp
              have hv2B : v2 ∈ B := by rw [hB_eq]; simp
              have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
              exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
            · exact edge_in_triangle_sym2 t v1 v2 hv1_in hz_in
          · -- z = b: use {v1, b}
            use s(v1, b)
            constructor
            · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                         true_or, or_true, true_and]
              have hv1B : v1 ∈ B := by rw [hB_eq]; simp
              have hbB : b ∈ B := by rw [hB_eq]; simp
              have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
              exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hbB hbv1.symm)
            · exact edge_in_triangle_sym2 t v1 b hv1_in hz_in
    · -- x ∈ {a1, a2}, not v1
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · -- x = a1: use {v1, a1}
        use s(v1, a1)
        constructor
        · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                     true_or, or_true, true_and]
          have hv1A : v1 ∈ A := by rw [hA_eq]; simp
          have ha1A : a1 ∈ A := by rw [hA_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
        · exact edge_in_triangle_sym2 t v1 a1 hv1_in hx.1
      · -- x = a2: similar to the y = a2 case above
        -- Get the third vertex z
        obtain ⟨z, hz_in, hz_ne_v1, hz_ne_a2⟩ := third_vertex_exists t ht_card v1 a2 hv1_in hx.1 ha2v1.symm
        have hz_adj_v1 : G.Adj v1 z := ht_clique.1 hv1_in hz_in hz_ne_v1
        rcases h_v1_neighbors z hz_adj_v1 with hz_A | hz_B
        · rw [hA_eq] at hz_A
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz_A
          rcases hz_A with rfl | rfl | rfl
          · exact absurd rfl hz_ne_v1
          · use s(v1, a1)
            constructor
            · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                         true_or, or_true, true_and]
              have hv1A : v1 ∈ A := by rw [hA_eq]; simp
              have ha1A : a1 ∈ A := by rw [hA_eq]; simp
              have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
              exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1A ha1A ha1v1.symm)
            · exact edge_in_triangle_sym2 t v1 a1 hv1_in hz_in
          · exact absurd rfl hz_ne_a2
        · rw [hB_eq] at hz_B
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz_B
          rcases hz_B with rfl | rfl | rfl
          · exact absurd rfl hz_ne_v1
          · use s(v1, v2)
            constructor
            · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                         true_or, or_true, true_and]
              have hv1B : v1 ∈ B := by rw [hB_eq]; simp
              have hv2B : v2 ∈ B := by rw [hB_eq]; simp
              have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
              exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
            · exact edge_in_triangle_sym2 t v1 v2 hv1_in hz_in
          · use s(v1, b)
            constructor
            · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                         true_or, or_true, true_and]
              have hv1B : v1 ∈ B := by rw [hB_eq]; simp
              have hbB : b ∈ B := by rw [hB_eq]; simp
              have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
              exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hbB hbv1.symm)
            · exact edge_in_triangle_sym2 t v1 b hv1_in hz_in

  · -- m = B: t shares edge with B = {v1, v2, b}
    rw [hB_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    by_cases hxv1 : x = v1
    · subst hxv1
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · -- y = v2: use {v1, v2}
        use s(v1, v2)
        constructor
        · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                     true_or, or_true, true_and]
          have hv1B : v1 ∈ B := by rw [hB_eq]; simp
          have hv2B : v2 ∈ B := by rw [hB_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
        · exact edge_in_triangle_sym2 t v1 v2 hv1_in hy.1
      · -- y = b: use {v1, b}
        use s(v1, b)
        constructor
        · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                     true_or, or_true, true_and]
          have hv1B : v1 ∈ B := by rw [hB_eq]; simp
          have hbB : b ∈ B := by rw [hB_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hbB hbv1.symm)
        · exact edge_in_triangle_sym2 t v1 b hv1_in hy.1
    · rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · use s(v1, v2)
        constructor
        · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                     true_or, or_true, true_and]
          have hv1B : v1 ∈ B := by rw [hB_eq]; simp
          have hv2B : v2 ∈ B := by rw [hB_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
        · exact edge_in_triangle_sym2 t v1 v2 hv1_in hx.1
      · use s(v1, b)
        constructor
        · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                     true_or, or_true, true_and]
          have hv1B : v1 ∈ B := by rw [hB_eq]; simp
          have hbB : b ∈ B := by rw [hB_eq]; simp
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hbB hbv1.symm)
        · exact edge_in_triangle_sym2 t v1 b hv1_in hx.1

  · -- m = C: t shares edge with C = {v2, v3, c}
    -- Since v1 ∈ t and v1 ∉ C, the two vertices in t ∩ C are from {v2, v3, c}
    -- So t = {v1, x, y} where x, y ∈ {v2, v3, c}
    rw [hC_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    -- t contains v1 and two vertices from C
    -- These two vertices from C form an edge of C, covered by {v2, v3} or {v3, c}
    rcases hx.2 with rfl | rfl | rfl <;> rcases hy.2 with rfl | rfl | rfl
    all_goals try exact absurd rfl hxy
    · -- x = v2, y = v3: use {v2, v3}
      use s(v2, v3)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv2C : v2 ∈ C := by rw [hC_eq]; simp
        have hv3C : v3 ∈ C := by rw [hC_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv2C hv3C hv23)
      · exact edge_in_triangle_sym2 t v2 v3 hx.1 hy.1
    · -- x = v2, y = c: need {v2, c}, not in cover8!
      -- But v1 is in t, adjacent to v2. So use {v1, v2}... wait, v1 might not be v2-adjacent in cover8 context
      -- Actually, by h_v1_neighbors, v2 ∈ A ∨ v2 ∈ B
      -- We know v2 ∈ B, so use {v1, v2}
      use s(v1, v2)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv1B : v1 ∈ B := by rw [hB_eq]; simp
        have hv2B : v2 ∈ B := by rw [hB_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
      · exact edge_in_triangle_sym2 t v1 v2 hv1_in hx.1
    · -- x = v3, y = v2: use {v2, v3}
      use s(v2, v3)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv2C : v2 ∈ C := by rw [hC_eq]; simp
        have hv3C : v3 ∈ C := by rw [hC_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv2C hv3C hv23)
      · exact edge_in_triangle_sym2 t v2 v3 hy.1 hx.1
    · -- x = v3, y = c: use {v3, c}
      use s(v3, c)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv3C : v3 ∈ C := by rw [hC_eq]; simp
        have hcC : c ∈ C := by rw [hC_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3C hcC hcv3.symm)
      · exact edge_in_triangle_sym2 t v3 c hx.1 hy.1
    · -- x = c, y = v2: use {v1, v2}
      use s(v1, v2)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv1B : v1 ∈ B := by rw [hB_eq]; simp
        have hv2B : v2 ∈ B := by rw [hB_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
      · exact edge_in_triangle_sym2 t v1 v2 hv1_in hy.1
    · -- x = c, y = v3: use {v3, c}
      use s(v3, c)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv3C : v3 ∈ C := by rw [hC_eq]; simp
        have hcC : c ∈ C := by rw [hC_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3C hcC hcv3.symm)
      · exact edge_in_triangle_sym2 t v3 c hy.1 hx.1

  · -- m = D: t shares edge with D = {v3, d1, d2}
    rw [hD_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx.2 with rfl | rfl | rfl <;> rcases hy.2 with rfl | rfl | rfl
    all_goals try exact absurd rfl hxy
    · -- x = v3, y = d1: use {v3, d1}
      use s(v3, d1)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv3D : v3 ∈ D := by rw [hD_eq]; simp
        have hd1D : d1 ∈ D := by rw [hD_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hD_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3D hd1D hd1v3.symm)
      · exact edge_in_triangle_sym2 t v3 d1 hx.1 hy.1
    · -- x = v3, y = d2: need {v3, d2}, not in cover8
      -- Use {d1, d2} if d1 ∈ t... but we only know v3, d2 ∈ t
      -- Actually, v1 ∈ t and v3 ∈ t. By h_v1_neighbors, v3 ∈ A ∨ v3 ∈ B
      -- But hv1_not_C says v1 ∉ C, and hv1_not_D says v1 ∉ D
      -- This means v3 ∉ {a1, a2, b} (since those are in A or B but not at position v3)
      -- Actually we need to check: is v3 adjacent to v1?
      -- v3 is adjacent to v1 in t (since t is a clique)
      -- By h_v1_neighbors, v3 ∈ A ∨ v3 ∈ B
      -- v3 ∈ A = {v1, a1, a2} would mean v3 = v1 or v3 = a1 or v3 = a2
      -- v3 = v1 contradicts hv13
      -- v3 ∈ B = {v1, v2, b} would mean v3 = v1 or v3 = v2 or v3 = b
      -- v3 = v1 contradicts hv13, v3 = v2 contradicts hv23
      -- So either v3 = a1, v3 = a2, or v3 = b
      -- In PATH_4 structure, v3 is distinct from a1, a2, b (they're in different triangles)
      -- This is a CONTRADICTION - v3 cannot be adjacent to v1 in a proper PATH_4!
      -- Actually, this case (t shares edge with D while containing v1) should be impossible
      -- because v1 ∉ D and the only way t ∩ D has 2 elements is if both are from {v3, d1, d2}
      -- which doesn't include v1, so the third element of t must be v1
      -- But then v1 is adjacent to v3 (in t), and by h_v1_neighbors, v3 ∈ A ∨ v3 ∈ B
      -- In PATH_4, v3 ∉ A and v3 ∉ B (v3 is only in C and D)
      -- So this case leads to contradiction with h_v1_neighbors!
      exfalso
      have hv3_adj_v1 : G.Adj v1 v3 := ht_clique.1 hv1_in hx.1 hv13
      rcases h_v1_neighbors v3 hv3_adj_v1 with hv3_A | hv3_B
      · rw [hA_eq] at hv3_A
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv3_A
        rcases hv3_A with rfl | rfl | rfl
        · exact hv13 rfl
        · -- v3 = a1: but a1 and v3 should be distinct in PATH_4
          -- We need hypothesis for this
          sorry
        · -- v3 = a2: similar
          sorry
      · rw [hB_eq] at hv3_B
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv3_B
        rcases hv3_B with rfl | rfl | rfl
        · exact hv13 rfl
        · exact hv23.symm rfl
        · -- v3 = b: need hypothesis
          sorry
    · -- Symmetric cases
      use s(v3, d1)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hv3D : v3 ∈ D := by rw [hD_eq]; simp
        have hd1D : d1 ∈ D := by rw [hD_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hD_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv3D hd1D hd1v3.symm)
      · exact edge_in_triangle_sym2 t v3 d1 hy.1 hx.1
    · use s(d1, d2)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hd1D : d1 ∈ D := by rw [hD_eq]; simp
        have hd2D : d2 ∈ D := by rw [hD_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hD_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hd1D hd2D hd12)
      · exact edge_in_triangle_sym2 t d1 d2 hx.1 hy.1
    · exfalso
      have hv3_adj_v1 : G.Adj v1 v3 := ht_clique.1 hv1_in hy.1 hv13
      rcases h_v1_neighbors v3 hv3_adj_v1 with hv3_A | hv3_B
      · rw [hA_eq] at hv3_A
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv3_A
        rcases hv3_A with rfl | rfl | rfl
        · exact hv13 rfl
        · sorry
        · sorry
      · rw [hB_eq] at hv3_B
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv3_B
        rcases hv3_B with rfl | rfl | rfl
        · exact hv13 rfl
        · exact hv23.symm rfl
        · sorry
    · use s(d1, d2)
      constructor
      · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                   true_or, or_true, true_and]
        have hd1D : d1 ∈ D := by rw [hD_eq]; simp
        have hd2D : d2 ∈ D := by rw [hD_eq]; simp
        have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hD_clique
        exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hd1D hd2D hd12)
      · exact edge_in_triangle_sym2 t d1 d2 hy.1 hx.1

end
