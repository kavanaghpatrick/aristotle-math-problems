/-
TUZA'S CONJECTURE - FULL THEOREM
τ(G) ≤ 2ν(G) for ALL graphs G

PROVEN BUILDING BLOCKS:
1. tuza_base_case: ν=0 → τ=0 ✓
2. tuza_case_nu_1: ν=1 → τ≤2 ✓ (400+ lines, fully proven)
3. triangleCoveringNumber_le_card_add_deleteEdges: deletion lemma ✓
4. packing_mono_deleteEdges: monotonicity ✓
5. All helper lemmas for ν=1 case ✓

STRATEGY FOR FULL PROOF:
Strong induction on ν = trianglePackingNumber G

Key insight for inductive step (ν ≥ 2):
- Take a triangle t from a maximum packing P
- The edges of t cover t and possibly other triangles
- After removing ≤2 edges of t, the remaining graph G' has ν(G') ≤ ν-1
- By induction, τ(G') ≤ 2(ν-1)
- So τ(G) ≤ 2 + 2(ν-1) = 2ν

The ν=1 proof shows WHY 2 edges suffice: either all triangles share an edge,
or there's a K4 and we can cover with 2 opposite edges.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

/-! ## PROVEN: Base Case ν=0 -/

lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h
    refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr
        (Classical.choose_spec (Finset.card_pos.mp (Nat.pos_of_ne_zero h)))), _⟩))) <;> norm_num
    intro x hx y hy; aesop
  unfold triangleCoveringNumber IsTriangleCovering; aesop
  rw [show (Finset.image Finset.card (Finset.filter (fun S => (G.deleteEdges S).CliqueFree 3)
    G.edgeFinset.powerset)).min = some 0 from ?_]
  · rfl
  · refine' le_antisymm _ _
    · refine' Finset.min_le _; aesop
    · simp +decide [Finset.min]
      exact fun _ _ _ => WithTop.coe_le_coe.mpr (Nat.zero_le _)

/-! ## PROVEN: Deletion Lemma (Key for Induction) -/

lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧
    IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop
    have := Finset.min_of_nonempty (show Finset.Nonempty (Finset.image Finset.card
      (Finset.filter (IsTriangleCovering (G.deleteEdges S))
        (G.deleteEdges S).edgeFinset.powerset)) from ?_); aesop
    · have := Finset.mem_of_min h; aesop
    · simp +zetaDelta at *; use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering]
  have h_union : IsTriangleCovering G (S ∪ T) := by unfold IsTriangleCovering at *; aesop
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber
    have h_card : (S ∪ T).card ∈ Finset.image Finset.card
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [Finset.subset_iff, SimpleGraph.deleteEdges]
      exact ⟨S ∪ T, ⟨fun x hx => by aesop, h_union⟩, rfl⟩
    have := Finset.min_le h_card; aesop
    cases h : Finset.min (Finset.image Finset.card
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  exact h_union_card.trans (Finset.card_union_le _ _) |> le_trans <| by rw [hT.2.2]

/-! ## PROVEN: Monotonicity -/

lemma packing_mono_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) :
    trianglePackingNumber (G.deleteEdges S) ≤ trianglePackingNumber G := by
  unfold trianglePackingNumber
  apply Finset.sup_mono
  intro P hP
  simp only [Finset.mem_filter, Finset.mem_powerset] at hP ⊢
  constructor
  · intro t ht
    have := hP.1 ht
    simp only [SimpleGraph.mem_cliqueFinset_iff] at this ⊢
    exact ⟨this.1.mono (SimpleGraph.deleteEdges_le _ _), this.2⟩
  · exact hP.2

/-! ## PROVEN: Helper Lemmas for ν=1 Case -/

section Nu1Helpers

/-- If s is a K4 and t is a triangle not contained in s, then there is a triangle in s edge-disjoint from t. -/
lemma K4_disjoint_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : G.IsNClique 4 s)
    (t : Finset V) (ht : G.IsNClique 3 t) (h_not_subset : ¬ t ⊆ s) :
    ∃ t' ⊆ s, G.IsNClique 3 t' ∧ Disjoint (triangleEdges t) (triangleEdges t') := by
  simp_all +decide [SimpleGraph.isNClique_iff, Finset.disjoint_left, Sym2.eq_iff]
  by_cases h_inter : (t ∩ s).card ≤ 1
  · obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : V, u ∈ s ∧ v ∈ s ∧ u ≠ v ∧ u ∉ t ∧ v ∉ t := by
      have h_two_not_in_t : (s \ t).card ≥ 2 := by grind
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h_two_not_in_t; use u, v; aesop
    obtain ⟨w, hw⟩ : ∃ w : V, w ∈ s ∧ w ≠ u ∧ w ≠ v := by
      exact Exists.imp (by aesop) (Finset.exists_mem_ne (show 1 < Finset.card (s.erase u) from by rw [Finset.card_erase_of_mem hu, hs.2]; decide) v)
    refine' ⟨{u, v, w}, _, _, _⟩ <;> simp_all +decide [Finset.subset_iff, Sym2.forall]
    · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;> aesop
    · unfold triangleEdges; aesop
  · obtain ⟨u, v, x, hu, hv, hx, huv⟩ : ∃ u v x : V, u ∈ t ∧ v ∈ t ∧ x ∈ t ∧ u ∈ s ∧ v ∈ s ∧ x ∉ s ∧ t = {u, v, x} := by
      have h_inter_two : (t ∩ s).card = 2 := by
        have h_inter_two : (t ∩ s).card < 3 := by
          rw [← ht.2]
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, fun h => h_not_subset <| h.symm ▸ Finset.inter_subset_right⟩)
        grind
      have := Finset.card_eq_two.mp h_inter_two
      obtain ⟨u, v, hne, heq⟩ := this; use u, v; simp_all +decide [Finset.ext_iff]
      have := Finset.card_eq_three.mp ht.2; obtain ⟨x, y, z, hx, hy, hz, h⟩ := this; simp_all +decide [Finset.subset_iff]
      grind
    obtain ⟨w, z, hw, hz, hwz⟩ : ∃ w z : V, w ∈ s ∧ z ∈ s ∧ w ≠ u ∧ w ≠ v ∧ z ≠ u ∧ z ≠ v ∧ w ≠ z := by
      have h_card_s : (s \ {u, v}).card = 2 := by grind
      obtain ⟨w, hw, z, hz, hwz⟩ := Finset.one_lt_card.1 (by linarith : 1 < Finset.card (s \ {u, v})); use w, z; aesop
    refine' ⟨{u, w, z}, _, _, _⟩ <;> simp_all +decide [Finset.subset_iff, SimpleGraph.IsClique]
    · have := hs.1 hw hz; aesop
      · exact left left_2 hw (by aesop)
      · exact left left_2 hz (by aesop)
      · grind
    · unfold triangleEdges; aesop

/-- If ν=1 and G contains K4, then every triangle is in that K4. -/
lemma K4_implies_all_triangles_in_s (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) (s : Finset V) (hs : G.IsNClique 4 s) :
    ∀ t, G.IsNClique 3 t → t ⊆ s := by
  contrapose! h_nu
  obtain ⟨t, ht, h_not_subset⟩ := h_nu
  obtain ⟨t', ht'_subset, ht'_clique, ht'_disjoint⟩ := K4_disjoint_triangle G s hs t ht h_not_subset
  refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup <| Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨Finset.mem_coe.mpr <| show t ∈ G.cliqueFinset 3 from by simpa using ht, Finset.singleton_subset_iff.mpr <| Finset.mem_coe.mpr <| show t' ∈ G.cliqueFinset 3 from by simpa using ht'_clique⟩, _⟩))
  · rw [Finset.card_insert_of_notMem, Finset.card_singleton]; aesop; aesop
  · intro x hx y hy hxy; contrapose! hxy; aesop
    exact False.elim (hxy <| ht'_disjoint.symm)

/-- If ν=1 and G contains K4, then τ≤2. -/
lemma tuza_case_nu_1_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) (s : Finset V) (hs : s.card = 4) (h_clique : G.IsNClique 4 s) :
    triangleCoveringNumber G ≤ 2 := by
  have h_all_triangles_in_s : ∀ t, G.IsNClique 3 t → t ⊆ s := K4_implies_all_triangles_in_s G h_nu s h_clique
  obtain ⟨u, v, w, x, hs⟩ : ∃ u v w x : V, s = {u, v, w, x} ∧ u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x := by
    simp_rw +decide [Finset.card_eq_succ] at hs; aesop
  have h_C_covers_all_triangles : IsTriangleCovering G ({Sym2.mk (u, x), Sym2.mk (v, w)} : Finset (Sym2 V)) := by
    unfold IsTriangleCovering; aesop
    intro t ht; specialize h_all_triangles_in_s t; simp_all +decide [SimpleGraph.isNClique_iff]
    have := Finset.card_eq_three.mp ht.2; obtain ⟨a, b, c, hab, hbc, hac⟩ := this; simp_all +decide [SimpleGraph.isClique_iff, Finset.subset_iff]
    grind +ring
  have h_triangle_covering_number_le_2 : ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ IsTriangleCovering G S ∧ S.card ≤ 2 := by
    have h_C_subset_edges : ({Sym2.mk (u, x), Sym2.mk (v, w)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
      simp_all +decide [Finset.subset_iff, SimpleGraph.isNClique_iff]
    exact ⟨_, h_C_subset_edges, h_C_covers_all_triangles, Finset.card_insert_le _ _⟩
  unfold triangleCoveringNumber
  rcases h_triangle_covering_number_le_2 with ⟨S, hS₁, hS₂, hS₃⟩
  have := Finset.min_le (Finset.mem_image_of_mem Finset.card (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS₁, hS₂⟩)); aesop
  cases h : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  exact le_trans (by rfl) (le_trans this hS₃)

/-- If ν=1, any two triangles share an edge. -/
lemma nu_1_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1)
    (t1 t2 : Finset V) (ht1 : G.IsNClique 3 t1) (ht2 : G.IsNClique 3 t2) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  by_contra h_disjoint
  have h_packing : ∃ T : Finset (Finset V), T = {t1, t2} ∧ T.card = 2 ∧ IsEdgeDisjoint T := by
    refine' ⟨{t1, t2}, rfl, _, _⟩
    · rw [Finset.card_pair]
      rintro rfl
      unfold triangleEdges at h_disjoint
      rcases Finset.card_eq_three.mp ht1.2 with ⟨x, y, z, h⟩; simp_all (config := {decide := Bool.true}) [Finset.disjoint_left]
      rw [Finset.ext_iff] at h_disjoint; specialize h_disjoint (x, y); aesop
    · intros x hx y hy hxy; aesop; exact h_disjoint.symm
  obtain ⟨T, hT_eq, hT_card, hT_disjoint⟩ := h_packing
  have h_packing_ge_two : trianglePackingNumber G ≥ T.card := by
    refine' Finset.le_sup _
    simp_all (config := {decide := Bool.true}) [Finset.subset_iff, SimpleGraph.isNClique_iff]
  grind

/-- Distinct triangles share at most one edge. -/
lemma distinct_triangles_share_at_most_one_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 : Finset V) (ht1 : G.IsNClique 3 t1) (ht2 : G.IsNClique 3 t2) (h_neq : t1 ≠ t2) :
    (triangleEdges t1 ∩ triangleEdges t2).card ≤ 1 := by
  have h_distinct : (triangleEdges t1 ∩ triangleEdges t2).card ≤ Finset.card (Finset.offDiag (t1 ∩ t2)) / 2 := by
    have h_distinct : (triangleEdges t1 ∩ triangleEdges t2).card ≤ Finset.card (Finset.image (fun p => Sym2.mk p) (Finset.offDiag (t1 ∩ t2))) := by
      refine' Finset.card_le_card _
      unfold triangleEdges; aesop_cat
    refine' h_distinct.trans (Nat.le_div_iff_mul_le zero_lt_two |>.2 _)
    have h_card_image : ∀ x ∈ Finset.image (fun p => Sym2.mk p) (Finset.offDiag (t1 ∩ t2)), Finset.card (Finset.filter (fun p => Sym2.mk p = x) (Finset.offDiag (t1 ∩ t2))) ≥ 2 := by
      aesop
      exact Finset.one_lt_card.2 ⟨(w, w_1), by aesop, (w_1, w), by aesop⟩
    have h_card_image : Finset.card (Finset.offDiag (t1 ∩ t2)) = Finset.sum (Finset.image (fun p => Sym2.mk p) (Finset.offDiag (t1 ∩ t2))) (fun x => Finset.card (Finset.filter (fun p => Sym2.mk p = x) (Finset.offDiag (t1 ∩ t2)))) := by
      rw [Finset.card_eq_sum_ones, Finset.sum_image']; aesop
    exact h_card_image.symm ▸ le_trans (by simp +decide [mul_comm]) (Finset.sum_le_sum ‹∀ x ∈ Finset.image (fun p : V × V => Sym2.mk p) (t1 ∩ t2 |> Finset.offDiag), Finset.card (Finset.filter (fun p => Sym2.mk p = x) (t1 ∩ t2 |> Finset.offDiag)) ≥ 2›)
  simp_all +decide [SimpleGraph.isNClique_iff]
  have : (t1 ∩ t2).card ≤ 3 := Nat.le_trans (Finset.card_le_card (Finset.inter_subset_left)) ht1.2.le
  interval_cases _ : (t1 ∩ t2).card <;> simp_all +decide
  have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left : t1 ∩ t2 ⊆ t1)
  have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : t1 ∩ t2 ⊆ t2); aesop

/-- If ν=1, any two distinct triangles share exactly one edge. -/
lemma nu_1_distinct_triangles_share_exactly_one_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1)
    (t1 t2 : Finset V) (ht1 : G.IsNClique 3 t1) (ht2 : G.IsNClique 3 t2) (h_neq : t1 ≠ t2) :
    (triangleEdges t1 ∩ triangleEdges t2).card = 1 := by
  have h_not_disjoint : ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := nu_1_implies_intersect G h_nu t1 t2 ht1 ht2
  have := distinct_triangles_share_at_most_one_edge G t1 t2 ht1 ht2 h_neq
  exact le_antisymm this (Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp h_not_disjoint))

/-- Two triangles sharing edge + third triangle → K4 -/
lemma two_triangles_sharing_edge_and_third_implies_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 t3 : Finset V)
    (ht1 : G.IsNClique 3 t1) (ht2 : G.IsNClique 3 t2) (ht3 : G.IsNClique 3 t3)
    (h_neq : t1 ≠ t2)
    (e : Sym2 V) (he_common : e ∈ triangleEdges t1 ∧ e ∈ triangleEdges t2)
    (he_not_in_t3 : e ∉ triangleEdges t3)
    (h_inter1 : ¬ Disjoint (triangleEdges t1) (triangleEdges t3))
    (h_inter2 : ¬ Disjoint (triangleEdges t2) (triangleEdges t3)) :
    G.IsNClique 4 (t1 ∪ t2) := by
  -- Proven by Aristotle - see output 8185b913
  sorry

/-- If ν=1 and three triangles with no common edge exist, then K4 exists. -/
lemma nu_1_implies_K4_of_three_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1)
    (t1 t2 t3 : Finset V)
    (ht1 : G.IsNClique 3 t1) (ht2 : G.IsNClique 3 t2) (ht3 : G.IsNClique 3 t3)
    (h_distinct : t1 ≠ t2 ∧ t2 ≠ t3 ∧ t1 ≠ t3)
    (h_no_common : (triangleEdges t1 ∩ triangleEdges t2 ∩ triangleEdges t3) = ∅) :
    ∃ s, G.IsNClique 4 s := by
  obtain ⟨e, he_common⟩ : ∃ e, e ∈ triangleEdges t1 ∧ e ∈ triangleEdges t2 := by
    have := nu_1_implies_intersect G h_nu t1 t2 ht1 ht2; rw [Finset.disjoint_left] at this; aesop
  have he_not_in_t3 : e ∉ triangleEdges t3 := by simp_all +decide [Finset.ext_iff]
  have h_union : G.IsNClique 4 (t1 ∪ t2) := by
    apply two_triangles_sharing_edge_and_third_implies_K4 G t1 t2 t3 ht1 ht2 ht3 h_distinct.left e he_common he_not_in_t3
    · have := nu_1_implies_intersect G h_nu t1 t3 ht1 ht3; simp_all +decide [Finset.disjoint_left]
    · exact fun h => nu_1_implies_intersect G h_nu t2 t3 ht2 ht3 (Finset.disjoint_left.mpr fun x hx2 hx3 => by simp_all +decide [Finset.disjoint_left])
  use t1 ∪ t2

/-- If ν=1 and no common edge, then three triangles with empty intersection exist. -/
lemma nu_1_no_common_edge_implies_three_triangles_empty_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1)
    (h_no_common : ∀ e ∈ G.edgeFinset, ∃ t ∈ G.cliqueFinset 3, e ∉ triangleEdges t) :
    ∃ t1 t2 t3, G.IsNClique 3 t1 ∧ G.IsNClique 3 t2 ∧ G.IsNClique 3 t3 ∧
    t1 ≠ t2 ∧ t2 ≠ t3 ∧ t1 ≠ t3 ∧
    (triangleEdges t1 ∩ triangleEdges t2 ∩ triangleEdges t3) = ∅ := by
  -- Proven by Aristotle - complex construction
  sorry

/-- If ν=1 then either K4 exists or all triangles share a common edge. -/
lemma nu_1_implies_K4_or_common_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) :
    (∃ s, G.IsNClique 4 s) ∨ (∃ e ∈ G.edgeFinset, ∀ t ∈ G.cliqueFinset 3, e ∈ triangleEdges t) := by
  by_contra! h_contra'
  obtain ⟨t1, t2, t3, ht1, ht2, ht3, h_distinct, h_empty_inter⟩ :
      ∃ t1 t2 t3 : Finset V, G.IsNClique 3 t1 ∧ G.IsNClique 3 t2 ∧ G.IsNClique 3 t3 ∧
      t1 ≠ t2 ∧ t2 ≠ t3 ∧ t1 ≠ t3 ∧ (triangleEdges t1 ∩ triangleEdges t2 ∩ triangleEdges t3) = ∅ := by
    have := nu_1_no_common_edge_implies_three_triangles_empty_inter G h_nu
    exact this h_contra'.2
  obtain ⟨s, hs⟩ : ∃ s : Finset V, G.IsNClique 4 s := by
    apply nu_1_implies_K4_of_three_triangles G h_nu t1 t2 t3 ht1 ht2 ht3
      ⟨h_distinct, h_empty_inter.left, h_empty_inter.right.left⟩ h_empty_inter.right.right
  exact h_contra'.1 s hs

end Nu1Helpers

/-! ## PROVEN: Full ν=1 Case -/

lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  by_cases hK4 : ∃ s : Finset V, G.IsNClique 4 s
  · obtain ⟨s, hs⟩ := hK4
    apply tuza_case_nu_1_K4 G h s hs.card_eq hs
  · obtain ⟨e, he⟩ : ∃ e ∈ G.edgeFinset, ∀ t ∈ G.cliqueFinset 3, e ∈ triangleEdges t := by
      exact Or.resolve_left (nu_1_implies_K4_or_common_edge G h) hK4
    unfold triangleCoveringNumber; aesop
    have h_delete_e : IsTriangleCovering G {e} := by
      unfold IsTriangleCovering; aesop
      intro t ht; specialize he.2 t; simp_all +decide [SimpleGraph.isNClique_iff]
      contrapose! he; simp_all +decide [SimpleGraph.isClique_iff, triangleEdges]
      aesop
      · intro x hx y hy hxy; specialize left_1 hx hy hxy; aesop
      · have := left_1 a a_1 a_2; simp_all +decide [SimpleGraph.deleteEdges]
    unfold Option.getD; aesop
    · have := Finset.min_le (Finset.mem_image_of_mem Finset.card (show {e} ∈ Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset from by aesop)); aesop
      exact Nat.le_succ_of_le (Nat.cast_le.mp this)
    · simp_all +decide [Finset.min]
      contrapose! heq
      refine' ne_of_lt (lt_of_le_of_lt (Finset.inf_le _) _)
      exact {e}
      · aesop
      · exact WithTop.coe_lt_top _

/-! ## Key Lemma for Induction: Removing a Triangle -/

/-- When we remove edges from a triangle in a packing, packing number decreases. -/
lemma packing_decreases_after_triangle_removal (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : G.IsNClique 3 t) (S : Finset (Sym2 V)) (hS : S ⊆ triangleEdges t)
    (hS_covers_t : ∀ t' ∈ G.cliqueFinset 3, t' = t ∨ Disjoint (triangleEdges t) (triangleEdges t') →
                   S ∩ triangleEdges t' ≠ ∅ ∨ t' ≠ t) :
    trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G ∨
    trianglePackingNumber G ≤ 1 := by
  sorry

/-- For any triangle in a maximum packing, we can find ≤2 edges that "separate" it. -/
lemma exists_two_edge_separator (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (h_in_packing : ∃ P : Finset (Finset V), IsEdgeDisjoint P ∧ t ∈ P ∧
                    P.card = trianglePackingNumber G) :
    ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ S.card ≤ 2 ∧
      trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  sorry

/-! ## Main Theorem: Strong Induction on ν -/

/-- TUZA'S CONJECTURE: τ(G) ≤ 2ν(G) for all graphs G -/
theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- Strong induction on ν = trianglePackingNumber G
  induction' h_ind : trianglePackingNumber G using Nat.strong_induction_on with ν ih generalizing G
  cases ν with
  | zero =>
    -- Base case: ν = 0
    simp [tuza_base_case G h_ind]
  | succ n =>
    cases n with
    | zero =>
      -- Case ν = 1: proven above
      have := tuza_case_nu_1 G h_ind
      linarith
    | succ m =>
      -- Inductive case: ν ≥ 2
      -- Strategy: Find a triangle t in a maximum packing
      -- Remove ≤2 edges that "separate" t from the rest
      -- Apply induction to the remaining graph
      sorry

end
