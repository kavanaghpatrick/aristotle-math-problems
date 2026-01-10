/-
  slot295: PATH_4 Case 1 - Cover triangles containing v1

  SINGLE FOCUS: Prove that if v1 ∈ t, then one of {v1,a1}, {v1,a2}, {v1,v2} covers t

  KEY INSIGHT:
  If t is a triangle with v1 ∈ t and t ∉ M, then by maximality t shares an edge with
  some M-element. The only M-elements containing v1 are A and B.
  - If t shares edge with A: t ∩ A ⊇ {v1, x} for some x ∈ {a1, a2}
  - If t shares edge with B: t ∩ B ⊇ {v1, x} for some x ∈ {v2, b}

  So t contains v1 and at least one of {a1, a2, v2, b}.
  Our cover has {v1,a1}, {v1,a2}, {v1,v2} - so if t contains a1, a2, or v2, we're covered.

  REMAINING CASE: t = {v1, b, x} where x ∉ {a1, a2, v2}
  This t shares edge {v1,b} with B. But our cover doesn't have {v1,b}...

  WAIT - the cover10 doesn't have {v1,b}! We need to prove this case cannot occur,
  OR we need to add {v1,b} to the cover (making it 11 edges).

  ACTUALLY: Let's check - if t = {v1, b, x} and t ∉ M, t shares edge with some M-element.
  - With A? A = {v1, a1, a2}. t ∩ A = {v1} (since b, x ∉ A). |∩| = 1, not edge-sharing.
  - With B? B = {v1, v2, b}. t ∩ B = {v1, b}. |∩| = 2 ✓
  - With C? C = {v2, v3, c}. t ∩ C ⊆ {x} if x ∈ C. But then x ∈ {v2, v3, c}.
  - With D? D = {v3, d1, d2}. t ∩ D ⊆ {x} if x ∈ D.

  So t must share edge {v1,b} with B. The cover needs {v1,b} or {b,x} to cover t.
  Since we don't know x, we NEED {v1,b} in the cover.

  CONCLUSION: For τ ≤ 10, we need to include {v1,b} (and symmetrically {v3,c}).
  This changes the cover to:
  {a1,a2}, {v1,a1}, {v1,a2}, {v1,v2}, {v1,b},  -- 5 edges for A-B region
  {v2,v3}, {v2,b}, {v3,c},                     -- 3 edges for B-C region
  {d1,d2}, {v3,d1}, {v3,d2}                    -- 3 edges for C-D region

  Wait, that's 11 edges, which is > 10!

  Let me reconsider: maybe {v2,b} can cover the {v1,b,x} triangle if x = v2?
  If x = v2, then t = {v1, b, v2} = B, but t ∉ M by assumption, contradiction.
  So x ≠ v2, and {v2,b} doesn't help.

  NEW APPROACH: Use all 3 edges of each triangle endpoint!
  A = {v1,a1,a2}: edges {v1,a1}, {v1,a2}, {a1,a2} - 3 edges
  B = {v1,v2,b}: use {v1,v2}, {v2,b} - 2 edges (share v1-v2 with A)
  C = {v2,v3,c}: use {v2,v3}, {v3,c} - 2 edges
  D = {v3,d1,d2}: edges {v3,d1}, {v3,d2}, {d1,d2} - 3 edges

  Total: 10 edges, but this doesn't include {v1,b}!

  The issue is: triangles like {v1, b, x} need an edge incident to both v1 and b.
  Our cover has {v1,a1}, {v1,a2}, {v1,v2} at v1, but none of these contain b.

  FINAL REALIZATION: The cover10 in slot294 is INCORRECT for Case 1.
  We need to use the edge-sharing lemma to constrain which triangles can exist.
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

/-! ### Key Lemma: Triangles containing v1 have specific structure -/

/-
PROOF SKETCH for v1_triangle_neighbor:
1. t is a triangle containing v1, t ∉ M
2. By maximality, t shares edge with some m ∈ M
3. The only M-elements containing v1 are A = {v1,a1,a2} and B = {v1,v2,b}
4. If t shares edge with C or D, then t ∩ C ⊇ 2 or t ∩ D ⊇ 2
   But v1 ∉ C and v1 ∉ D (PATH_4 structure: A∩C = ∅, A∩D = ∅)
   So t ∩ C ⊆ t \ {v1} and t ∩ D ⊆ t \ {v1}
   Since t = {v1, x, y}, t \ {v1} = {x, y}
   For |t ∩ C| ≥ 2, need {x,y} ⊆ C, so x,y ∈ {v2,v3,c}
   For |t ∩ D| ≥ 2, need {x,y} ⊆ D, so x,y ∈ {v3,d1,d2}

5. So either t shares edge with A or B (in which case x or y is in {a1,a2,v2,b})
   OR t shares edge with C (x,y ∈ {v2,v3,c}) OR with D (x,y ∈ {v3,d1,d2})

6. In all cases, {x,y} ∩ {a1,a2,v2,b,v3,c,d1,d2} ≠ ∅
-/
lemma v1_triangle_neighbor (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    -- PATH_4 disjointness (non-adjacent triangles share no vertices)
    (hAC_disj : A ∩ C = ∅) (hAD_disj : A ∩ D = ∅) (hBD_disj : B ∩ D = ∅)
    (ht : t ∈ G.cliqueFinset 3) (hv1_in : v1 ∈ t) (ht_not : t ∉ M) :
    ∃ w ∈ ({a1, a2, v2, b} : Finset V), w ∈ t ∧ w ≠ v1 := by
  -- By maximality, t shares edge with some M-element
  obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_not
  -- Get two distinct vertices in t ∩ m
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
  simp only [Finset.mem_inter] at hx hy
  -- Determine which M-element m is
  rw [hM_eq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · -- m = A: t shares edge with A = {v1, a1, a2}
    -- Since v1 ∈ t and |t ∩ A| ≥ 2, at least one of a1, a2 is in t
    rw [hA_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    by_cases hxv1 : x = v1
    · -- x = v1, so y ∈ {a1, a2} and y ∈ t
      subst hxv1
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · use a1; simp; exact ⟨hy.1, fun h => hxy h.symm⟩
      · use a2; simp; exact ⟨hy.1, fun h => hxy h.symm⟩
    · -- x ≠ v1, so x ∈ {a1, a2} and x ∈ t
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · use a1; simp; exact ⟨hx.1, hxv1⟩
      · use a2; simp; exact ⟨hx.1, hxv1⟩
  · -- m = B: t shares edge with B = {v1, v2, b}
    rw [hB_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    by_cases hxv1 : x = v1
    · subst hxv1
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · use v2; simp; exact ⟨hy.1, fun h => hxy h.symm⟩
      · use b; simp; exact ⟨hy.1, fun h => hxy h.symm⟩
    · rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · use v2; simp; exact ⟨hx.1, hxv1⟩
      · use b; simp; exact ⟨hx.1, hxv1⟩
  · -- m = C: t shares edge with C = {v2, v3, c}
    -- But v1 ∈ t and A ∩ C = ∅, so v1 ∉ C
    -- This means |t ∩ C| counts vertices OTHER than v1
    -- Need to show one of {v2, v3, c} is in t (and use v2)
    rw [hC_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    -- x, y ∈ t ∩ C ⊆ C = {v2, v3, c}
    -- At least one of x, y is v2 (if v2 ∈ t) or both are in {v3, c}
    rcases hx.2 with rfl | rfl | rfl
    · use v2; simp; exact ⟨hx.1, ?_⟩
      -- need v2 ≠ v1
      sorry -- requires distinctness hypothesis
    · -- x = v3
      rcases hy.2 with rfl | rfl | rfl
      · use v2; simp; exact ⟨hy.1, ?_⟩; sorry
      · -- both x, y ∈ {v3, c}, need to show v3 or c is in our target set
        -- Target is {a1, a2, v2, b}, v3 is NOT in this set!
        -- This case needs more careful handling...
        sorry
      · sorry
    · sorry
  · -- m = D: similar to C case
    sorry

end
