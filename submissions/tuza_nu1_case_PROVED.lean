/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: beae6b6a-05b7-4efb-b12e-b9581793032a
-/

/-
ITERATION 3 for Tuza's Conjecture - τ ≤ 2ν
Previous: c7732074-b171-431b-a9fe-be3726332982

KEY FIX: Completing the k4_is_maximal_if_nu_1 lemma

The logic:
1. We have K₄ on {u,v,w,x} with ν=1
2. Any triangle t must share an edge with every K₄ triangle (since ν=1)
3. If t ∉ {K₄ triangles}, then t uses a vertex y ∉ {u,v,w,x}
4. Then t = {a,b,y} for some a,b ∈ {u,v,w,x}
5. t only shares edge {a,b} with K₄, but some K₄ triangles don't contain {a,b}
6. So t would be edge-disjoint from those triangles, giving ν≥2, contradiction
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

def triangleEdges {V : Type} [DecidableEq V] (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint {V : Type} [DecidableEq V] (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

noncomputable def trianglePackingNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

noncomputable def triangleCoveringNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

-- All supporting lemmas from previous iteration (proven by Aristotle)

lemma tuza_base_case {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h;
    refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ( Classical.choose_spec ( Finset.card_pos.mp ( Nat.pos_of_ne_zero h ) ) ) ), _ ⟩ ) ) ) <;> norm_num;
    intro x hx y hy; aesop;
  unfold triangleCoveringNumber;
  unfold IsTriangleCovering; aesop;
  rw [ show ( Finset.image Finset.card ( Finset.filter ( fun S : Finset ( Sym2 V ) => ( G.deleteEdges ( S : Set ( Sym2 V ) ) ).CliqueFree 3 ) ( G.edgeFinset.powerset ) ) ).min = some 0 from ?_ ];
  · rfl;
  · refine' le_antisymm _ _;
    · refine' Finset.min_le _ ; aesop;
    · simp +decide [ Finset.min ];
      exact fun _ _ _ => WithTop.coe_le_coe.mpr ( Nat.zero_le _ )

lemma triangleCoveringNumber_le_card_add_deleteEdges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧ IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop;
    have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering ( G.deleteEdges ( S : Set ( Sym2 V ) ) ) ) ( G.deleteEdges ( S : Set ( Sym2 V ) ) |> SimpleGraph.edgeFinset |> Finset.powerset ) ) ) from ?_ ) ; aesop;
    · have := Finset.mem_of_min h; aesop;
    · simp +zetaDelta at *;
      use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering];
  have h_union : IsTriangleCovering G (S ∪ T) := by
    unfold IsTriangleCovering at *; aesop;
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber;
    have h_union_card : (S ∪ T).card ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [ Finset.subset_iff, SimpleGraph.deleteEdges ];
      exact ⟨ S ∪ T, ⟨ fun x hx => by aesop, h_union ⟩, rfl ⟩;
    have := Finset.min_le h_union_card; aesop;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
  exact h_union_card.trans ( Finset.card_union_le _ _ ) |> le_trans <| by rw [ hT.2.2 ] ;

lemma exists_max_packing {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_exists_packing : ∃ P : Finset (Finset V), P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
    have h_finite : (G.cliqueFinset 3).powerset.Nonempty := by
      exact ⟨ ∅, Finset.mem_powerset.mpr <| Finset.empty_subset _ ⟩
    have h_exists_packing : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧ ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card := by
      exact Finset.exists_max_image _ _ ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide [ IsEdgeDisjoint ] ⟩ ⟩;
    obtain ⟨ P, hP₁, hP₂ ⟩ := h_exists_packing; use P; aesop;
    exact le_antisymm ( Finset.le_sup ( f := Finset.card ) ( by aesop ) ) ( Finset.sup_le fun Q hQ => by aesop );
  exact h_exists_packing

lemma packing_one_implies_intersect {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  contrapose! h;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨ h1, Finset.singleton_subset_iff.mpr h2 ⟩, _ ⟩ ) );
  · rw [ Finset.card_pair ] ; aesop;
    unfold triangleEdges at h; aesop;
    simp_all +decide [ Finset.ext_iff ];
    have := Finset.card_eq_three.mp h2.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; specialize h a b; aesop;
  · intro x hx y hy hxy; aesop;
    exact h.symm

lemma k4_tau_le_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w x : V) (h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x)
    (h_edges : G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x)
    (h_triangles : G.cliqueFinset 3 = { {u,v,w}, {u,v,x}, {u,w,x}, {v,w,x} }) :
    triangleCoveringNumber G ≤ 2 := by
  have h_delete_edges : IsTriangleCovering G ({Sym2.mk (u, v), Sym2.mk (w, x)} : Finset (Sym2 V)) := by
    simp_all +decide [ Finset.ext_iff, IsTriangleCovering ];
    simp_all +decide [ SimpleGraph.isNClique_iff ];
    intro a ha; specialize h_triangles a; simp_all +decide [ SimpleGraph.isClique_iff, Set.Pairwise ] ;
    grind;
  unfold triangleCoveringNumber;
  have h_card : 2 ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
    simp +zetaDelta at *;
    refine' ⟨ { Sym2.mk ( u, v ), Sym2.mk ( w, x ) }, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
  have := Finset.min_le h_card; aesop;
  cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop

noncomputable section AristotleLemmas

lemma intersect_triangles_aux {V : Type} [DecidableEq V] (u v w x y : V)
    (h_distinct : u ≠ v ∧ v ≠ w ∧ w ≠ u)
    (h_x : x ≠ u ∧ x ≠ v ∧ x ≠ w)
    (h_y : y ≠ v ∧ y ≠ w ∧ y ≠ u)
    (h_inter : ¬ Disjoint (triangleEdges {u, v, x}) (triangleEdges {v, w, y})) :
    x = y := by
      unfold triangleEdges at h_inter;
      rw [ Finset.disjoint_left ] at h_inter ; aesop

end AristotleLemmas

lemma k4_of_intersecting_triangles {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w : V) (h_distinct : u ≠ v ∧ v ≠ w ∧ w ≠ u)
    (T0 : Finset V) (hT0 : T0 = {u, v, w}) (hT0_in : T0 ∈ G.cliqueFinset 3)
    (T1 T2 T3 : Finset V)
    (hT1_in : T1 ∈ G.cliqueFinset 3) (hT2_in : T2 ∈ G.cliqueFinset 3) (hT3_in : T3 ∈ G.cliqueFinset 3)
    (hT1_edges : Sym2.mk (u, v) ∈ triangleEdges T1 ∧ Sym2.mk (v, w) ∉ triangleEdges T1 ∧ Sym2.mk (w, u) ∉ triangleEdges T1)
    (hT2_edges : Sym2.mk (v, w) ∈ triangleEdges T2 ∧ Sym2.mk (w, u) ∉ triangleEdges T2 ∧ Sym2.mk (u, v) ∉ triangleEdges T2)
    (hT3_edges : Sym2.mk (w, u) ∈ triangleEdges T3 ∧ Sym2.mk (u, v) ∉ triangleEdges T3 ∧ Sym2.mk (v, w) ∉ triangleEdges T3)
    (h_inter_12 : ¬ Disjoint (triangleEdges T1) (triangleEdges T2))
    (h_inter_23 : ¬ Disjoint (triangleEdges T2) (triangleEdges T3))
    (h_inter_31 : ¬ Disjoint (triangleEdges T3) (triangleEdges T1)) :
    ∃ x, x ≠ u ∧ x ≠ v ∧ x ≠ w ∧
      T1 = {u, v, x} ∧ T2 = {v, w, x} ∧ T3 = {w, u, x} ∧
      G.Adj u x ∧ G.Adj v x ∧ G.Adj w x := by
  obtain ⟨x, hx⟩ : ∃ x, x ≠ u ∧ x ≠ v ∧ x ≠ w ∧ T1 = {u, v, x} := by
    unfold triangleEdges at *;
    simp_all +decide [ Finset.mem_image, Sym2.eq ];
    obtain ⟨a, b, c, habc⟩ : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ T1 = {a, b, c} := by
      have hT1_card : T1.card = 3 := by
        exact hT1_in.2;
      rw [ Finset.card_eq_three ] at hT1_card; tauto;
    rcases hT1_edges.1 with ⟨ x, y, hxy, h ⟩ ; simp_all ( config := { decide := Bool.true } ) [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
    grind +ring
  obtain ⟨y, hy⟩ : ∃ y, y ≠ v ∧ y ≠ w ∧ y ≠ u ∧ T2 = {v, w, y} := by
    have hT2_card : T2.card = 3 := by
      aesop;
      exact hT2_in.card_eq;
    have hT2_subset : v ∈ T2 ∧ w ∈ T2 ∧ u ∉ T2 := by
      unfold triangleEdges at *; simp_all +decide [ Finset.subset_iff ] ;
      grind;
    obtain ⟨ y, hy ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.insert_subset hT2_subset.1 ( Finset.insert_subset hT2_subset.2.1 ( Finset.empty_subset _ ) ), by aesop_cat ⟩ );
    use y; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hy.1 ( Finset.insert_subset hT2_subset.1 ( Finset.singleton_subset_iff.mpr hT2_subset.2.1 ) ) ) ; aesop;
  obtain ⟨z, hz⟩ : ∃ z, z ≠ w ∧ z ≠ u ∧ z ≠ v ∧ T3 = {w, u, z} := by
    obtain ⟨z, hz⟩ : ∃ z, T3 = {w, u, z} := by
      unfold triangleEdges at hT3_edges; simp_all +decide [ Finset.subset_iff ] ;
      rcases hT3_in with ⟨ hT3₁, hT3₂ ⟩ ; simp_all +decide [ Finset.card_insert_of_not_mem, SimpleGraph.isNClique_iff ] ;
      rw [ Finset.card_eq_three ] at hT3₂; obtain ⟨ a, b, c, ha, hb, hc, habc ⟩ := hT3₂; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
      grind +ring;
    use z;
    refine' ⟨ _, _, _, hz ⟩ <;> contrapose! hT3_edges <;> simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ];
    · simp_all +decide [ SimpleGraph.isNClique_iff ];
      rw [ Finset.card_insert_of_not_mem, Finset.card_singleton ] at hT3_in <;> aesop;
    · have := hT3_in.card_eq; simp_all +decide ;
    · unfold triangleEdges; simp +decide [ *, Sym2.eq_swap ] ;
  have hx_eq_y : x = y := by
    apply intersect_triangles_aux u v w x y;
    · tauto;
    · tauto;
    · tauto;
    · grind
  have hy_eq_z : y = z := by
    apply intersect_triangles_aux v w u y z;
    · tauto;
    · tauto;
    · tauto;
    · aesop
  have hx_eq_z : x = z := by
    grind
  simp_all ( config := { decide := Bool.true } ) [ SimpleGraph.cliqueFinset ];
  simp_all ( config := { decide := Bool.true } ) [ SimpleGraph.isNClique_iff, Finset.ext_iff ];
  grind

noncomputable section AristotleLemmas

lemma exists_triangle_disjoint_from_pair {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_tau : triangleCoveringNumber G > 2) (e1 e2 : Sym2 V) :
    ∃ T ∈ G.cliqueFinset 3, e1 ∉ triangleEdges T ∧ e2 ∉ triangleEdges T := by
      have h_cover : ∀ S : Finset (Sym2 V), S ⊆ G.edgeFinset → IsTriangleCovering G S → S.card ≥ 3 := by
        unfold triangleCoveringNumber at h_tau;
        contrapose! h_tau;
        have h_min : (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)).min ≤ 2 := by
          obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_tau;
          exact Finset.min_le ( Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS₁, hS₂ ⟩, rfl ⟩ ) |> le_trans <| by interval_cases S.card <;> trivial;
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
      contrapose! h_cover;
      use {e1, e2} ∩ G.edgeFinset;
      unfold IsTriangleCovering; aesop;
      · intro x hx;
        unfold triangleEdges at *; simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ] ;
        simp_all +decide [ SimpleGraph.isClique_iff, Set.Pairwise ];
        grind +ring;
      · exact lt_of_le_of_lt ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( by exact lt_of_le_of_lt ( Finset.card_insert_le _ _ ) ( by norm_num ) )

end AristotleLemmas

lemma exists_triangles_for_k4_of_tau_gt_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1)
    (h_tau : triangleCoveringNumber G > 2) :
    ∃ (u v w : V) (T0 T1 T2 T3 : Finset V),
      u ≠ v ∧ v ≠ w ∧ w ≠ u ∧
      T0 = {u, v, w} ∧ T0 ∈ G.cliqueFinset 3 ∧
      T1 ∈ G.cliqueFinset 3 ∧ T2 ∈ G.cliqueFinset 3 ∧ T3 ∈ G.cliqueFinset 3 ∧
      Sym2.mk (u, v) ∈ triangleEdges T1 ∧ Sym2.mk (v, w) ∉ triangleEdges T1 ∧ Sym2.mk (w, u) ∉ triangleEdges T1 ∧
      Sym2.mk (v, w) ∈ triangleEdges T2 ∧ Sym2.mk (w, u) ∉ triangleEdges T2 ∧ Sym2.mk (u, v) ∉ triangleEdges T2 ∧
      Sym2.mk (w, u) ∈ triangleEdges T3 ∧ Sym2.mk (u, v) ∉ triangleEdges T3 ∧ Sym2.mk (v, w) ∉ triangleEdges T3 := by
  obtain ⟨u, v, w, T0, hT0, hT0_in⟩ : ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ ∃ T0 : Finset V, T0 = {u, v, w} ∧ T0 ∈ G.cliqueFinset 3 := by
    have h_exists_triangle : ∃ T0 : Finset V, T0 ∈ G.cliqueFinset 3 := by
      contrapose! h_nu; aesop;
      unfold trianglePackingNumber at a;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      simp_all +decide [ Finset.filter_singleton, IsEdgeDisjoint ];
    obtain ⟨ T0, hT0 ⟩ := h_exists_triangle; rcases Finset.card_eq_three.mp ( G.mem_cliqueFinset_iff.mp hT0 |>.2 ) with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v, w; aesop;
  obtain ⟨T1, T2, T3, hT1, hT2, hT3⟩ : ∃ T1 T2 T3 : Finset V, T1 ∈ G.cliqueFinset 3 ∧ T2 ∈ G.cliqueFinset 3 ∧ T3 ∈ G.cliqueFinset 3 ∧ Sym2.mk (u, v) ∈ triangleEdges T1 ∧ Sym2.mk (v, w) ∉ triangleEdges T1 ∧ Sym2.mk (w, u) ∉ triangleEdges T1 ∧ Sym2.mk (v, w) ∈ triangleEdges T2 ∧ Sym2.mk (w, u) ∉ triangleEdges T2 ∧ Sym2.mk (u, v) ∉ triangleEdges T2 ∧ Sym2.mk (w, u) ∈ triangleEdges T3 ∧ Sym2.mk (u, v) ∉ triangleEdges T3 ∧ Sym2.mk (v, w) ∉ triangleEdges T3 := by
    obtain ⟨T1, hT1⟩ : ∃ T1 : Finset V, T1 ∈ G.cliqueFinset 3 ∧ Sym2.mk (u, v) ∈ triangleEdges T1 ∧ Sym2.mk (v, w) ∉ triangleEdges T1 ∧ Sym2.mk (w, u) ∉ triangleEdges T1 := by
      obtain ⟨T1, hT1⟩ : ∃ T1 ∈ G.cliqueFinset 3, ¬(Sym2.mk (v, w) ∈ triangleEdges T1 ∨ Sym2.mk (w, u) ∈ triangleEdges T1) := by
        have := exists_triangle_disjoint_from_pair G h_tau ( Sym2.mk ( v, w ) ) ( Sym2.mk ( w, u ) ) ; aesop;
      have := packing_one_implies_intersect G h_nu T1 { u, v, w } ; simp_all +decide ;
      rw [ Finset.not_disjoint_iff ] at this;
      obtain ⟨ a, ha1, ha2 ⟩ := this;
      rcases a with ⟨ x, y ⟩ ; simp_all +decide [ triangleEdges ] ;
      grind
    obtain ⟨T2, hT2⟩ : ∃ T2 : Finset V, T2 ∈ G.cliqueFinset 3 ∧ Sym2.mk (v, w) ∈ triangleEdges T2 ∧ Sym2.mk (w, u) ∉ triangleEdges T2 ∧ Sym2.mk (u, v) ∉ triangleEdges T2 := by
      obtain ⟨T2, hT2⟩ : ∃ T2 : Finset V, T2 ∈ G.cliqueFinset 3 ∧ Sym2.mk (w, u) ∉ triangleEdges T2 ∧ Sym2.mk (u, v) ∉ triangleEdges T2 := by
        exact Exists.imp ( by tauto ) ( exists_triangle_disjoint_from_pair G h_tau ( Sym2.mk ( w, u ) ) ( Sym2.mk ( u, v ) ) );
      have hT2_inter : ¬ Disjoint (triangleEdges T2) (triangleEdges {u, v, w}) := by
        apply packing_one_implies_intersect G h_nu T2 {u, v, w};
        · exact hT2.1;
        · aesop;
      unfold triangleEdges at *; simp_all +decide [ Finset.disjoint_left ] ;
      rcases hT2_inter with ⟨ x, y, hy, z, hz, hyz, rfl, h | h | h | h ⟩ <;> simp_all +decide [ Sym2.eq_iff ];
      · grind +ring;
      · grind;
      · grind;
      · grind +ring
    obtain ⟨T3, hT3⟩ : ∃ T3 : Finset V, T3 ∈ G.cliqueFinset 3 ∧ Sym2.mk (w, u) ∈ triangleEdges T3 ∧ Sym2.mk (u, v) ∉ triangleEdges T3 ∧ Sym2.mk (v, w) ∉ triangleEdges T3 := by
      obtain ⟨T3, hT3⟩ : ∃ T3 : Finset V, T3 ∈ G.cliqueFinset 3 ∧ ¬(Sym2.mk (u, v) ∈ triangleEdges T3) ∧ ¬(Sym2.mk (v, w) ∈ triangleEdges T3) := by
        exact Exists.imp ( by aesop ) ( exists_triangle_disjoint_from_pair G h_tau ( Sym2.mk ( u, v ) ) ( Sym2.mk ( v, w ) ) );
      have hT3_inter : ¬ Disjoint (triangleEdges T3) (triangleEdges {u, v, w}) := by
        have := packing_one_implies_intersect G h_nu T3 { u, v, w } ; aesop;
      simp_all +decide [ Finset.disjoint_left, Sym2.eq_swap ];
      simp_all +decide [ triangleEdges ];
      rcases hT3_inter with ⟨ x, ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩, c, d, ⟨ hc, hd, hcd ⟩, hx ⟩ ; simp_all +decide [ Sym2.eq_swap ] ;
      grind +ring;
    exact ⟨ T1, T2, T3, hT1.1, hT2.1, hT3.1, hT1.2.1, hT1.2.2.1, hT1.2.2.2, hT2.2.1, hT2.2.2.1, hT2.2.2.2, hT3.2.1, hT3.2.2.1, hT3.2.2.2 ⟩;
  exact ⟨ u, v, w, { u, v, w }, T1, T2, T3, T0, hT0, hT0_in.1, rfl, hT0_in.2.choose_spec.1 ▸ hT0_in.2.choose_spec.2, hT1, hT2, hT3.1, hT3.2 ⟩

/-
KEY LEMMA - k4_is_maximal_if_nu_1
If we have K₄ on {u,v,w,x} and ν=1, then these are the ONLY triangles in G.

Proof sketch:
1. The K₄ triangles are {u,v,w}, {u,v,x}, {u,w,x}, {v,w,x}
2. These 4 triangles cover all 6 edges of K₄
3. Any triangle t must share an edge with each of these (since ν=1)
4. If t uses only vertices from {u,v,w,x}, it must be one of the 4 K₄ triangles
5. If t uses a vertex y ∉ {u,v,w,x}:
   - t = {a,b,y} for some a,b ∈ {u,v,w,x}
   - t shares at most edge {a,b} with K₄
   - But there's a K₄ triangle that doesn't contain {a,b}
   - So t would be edge-disjoint from that triangle (ν≥2), contradiction

HINT FOR ARISTOTLE:
- Use `packing_one_implies_intersect` to show any triangle shares an edge with each K₄ triangle
- Case split on whether the triangle uses only K₄ vertices or has an external vertex
- For external vertex case, show the triangle can't share edges with all K₄ triangles
-/
lemma k4_is_maximal_if_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w x : V) (h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x)
    (h_edges : G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x)
    (h_nu_1 : trianglePackingNumber G = 1) :
    ∀ t ∈ G.cliqueFinset 3, t ∈ ({ {u,v,w}, {u,v,x}, {u,w,x}, {v,w,x} } : Finset (Finset V)) := by
  intro t ht
  -- First, get that t is a 3-clique with vertices a, b, c
  have ht_card : t.card = 3 := ht.2
  obtain ⟨a, b, c, hab, hac, hbc, ht_eq⟩ := Finset.card_eq_three.mp ht_card
  -- t must share an edge with the K₄ triangle {u,v,w}
  have h_uvw_in : ({u,v,w} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  have h_inter_uvw : ¬ Disjoint (triangleEdges t) (triangleEdges {u,v,w}) := by
    exact packing_one_implies_intersect G h_nu_1 t {u,v,w} ht h_uvw_in
  -- Similarly for other K₄ triangles
  have h_uvx_in : ({u,v,x} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  have h_inter_uvx : ¬ Disjoint (triangleEdges t) (triangleEdges {u,v,x}) := by
    exact packing_one_implies_intersect G h_nu_1 t {u,v,x} ht h_uvx_in
  have h_uwx_in : ({u,w,x} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  have h_inter_uwx : ¬ Disjoint (triangleEdges t) (triangleEdges {u,w,x}) := by
    exact packing_one_implies_intersect G h_nu_1 t {u,w,x} ht h_uwx_in
  have h_vwx_in : ({v,w,x} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  have h_inter_vwx : ¬ Disjoint (triangleEdges t) (triangleEdges {v,w,x}) := by
    exact packing_one_implies_intersect G h_nu_1 t {v,w,x} ht h_vwx_in
  -- Now analyze: t must share an edge with each of the 4 K₄ triangles
  -- The K₄ edges are: {u,v}, {u,w}, {u,x}, {v,w}, {v,x}, {w,x}
  -- Each K₄ triangle has exactly 3 of these edges
  -- If t has a vertex y ∉ {u,v,w,x}, then t's edges involving y can't be K₄ edges
  -- So t must share its edges that are within {u,v,w,x} with ALL K₄ triangles
  -- But t has at most 3 edges total, so t ⊆ {u,v,w,x}
  -- And if t ⊆ {u,v,w,x} and t is a 3-clique, t must be one of the 4 K₄ triangles
  simp_all +decide [triangleEdges, Finset.disjoint_left, Finset.mem_image]
  -- t shares an edge with {u,v,w}, {u,v,x}, {u,w,x}, {v,w,x}
  -- This constrains t heavily
  simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  simp_all +decide [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton]
  -- At this point, t = {a,b,c} must be one of the 4 K₄ triangles
  -- Use the intersection constraints to force this
  grind

lemma k4_implies_tau_le_2_if_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w x : V) (h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x)
    (h_edges : G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x)
    (h_nu_1 : trianglePackingNumber G = 1) :
    triangleCoveringNumber G ≤ 2 := by
  apply k4_tau_le_2 G u v w x h_distinct h_edges
  refine' Finset.Subset.antisymm _ _ <;> simp_all +decide [Finset.subset_iff]
  · have h_triangles : ∀ t ∈ G.cliqueFinset 3, t ∈ ({ {u,v,w}, {u,v,x}, {u,w,x}, {v,w,x} } : Finset (Finset V)) := by
      exact k4_is_maximal_if_nu_1 G u v w x h_distinct h_edges h_nu_1
    aesop
  · simp_all +decide [SimpleGraph.isNClique_iff]

lemma tuza_case_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  by_contra h_contra
  push_neg at h_contra
  have h_tau_gt_2 : triangleCoveringNumber G > 2 := by linarith
  obtain ⟨u, v, w, T0, T1, T2, T3, h_uv, h_vw, h_wu, hT0_eq, hT0_in, hT1_in, hT2_in, hT3_in,
          hT1_uv, hT1_vw, hT1_wu, hT2_vw, hT2_wu, hT2_uv, hT3_wu, hT3_uv, hT3_vw⟩ :=
    exists_triangles_for_k4_of_tau_gt_2 G h h_tau_gt_2
  -- Apply k4_of_intersecting_triangles to get the fourth vertex x
  have h_inter_12 : ¬ Disjoint (triangleEdges T1) (triangleEdges T2) := by
    exact packing_one_implies_intersect G h T1 T2 hT1_in hT2_in
  have h_inter_23 : ¬ Disjoint (triangleEdges T2) (triangleEdges T3) := by
    exact packing_one_implies_intersect G h T2 T3 hT2_in hT3_in
  have h_inter_31 : ¬ Disjoint (triangleEdges T3) (triangleEdges T1) := by
    exact packing_one_implies_intersect G h T3 T1 hT3_in hT1_in
  obtain ⟨x, hx_u, hx_v, hx_w, hT1_eq, hT2_eq, hT3_eq, h_ux, h_vx, h_wx⟩ :=
    k4_of_intersecting_triangles G u v w ⟨h_uv, h_vw, h_wu⟩ T0 hT0_eq hT0_in T1 T2 T3
      hT1_in hT2_in hT3_in
      ⟨hT1_uv, hT1_vw, hT1_wu⟩ ⟨hT2_vw, hT2_wu, hT2_uv⟩ ⟨hT3_wu, hT3_uv, hT3_vw⟩
      h_inter_12 h_inter_23 h_inter_31
  -- Now we have K₄ on {u,v,w,x}
  have h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x := by
    exact ⟨h_uv, h_wu.symm, hx_u.symm, h_vw, hx_v.symm, hx_w.symm⟩
  -- Get all K₄ edges from the clique membership
  have h_uv_edge : G.Adj u v := by
    have := hT0_in.1
    simp_all +decide [SimpleGraph.isClique_iff, Set.Pairwise]
  have h_uw_edge : G.Adj u w := by
    have := hT0_in.1
    simp_all +decide [SimpleGraph.isClique_iff, Set.Pairwise]
  have h_vw_edge : G.Adj v w := by
    have := hT0_in.1
    simp_all +decide [SimpleGraph.isClique_iff, Set.Pairwise]
  have h_edges : G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x := by
    exact ⟨h_uv_edge, h_uw_edge, h_ux, h_vw_edge, h_vx, h_wx⟩
  -- Apply k4_implies_tau_le_2_if_nu_1
  have h_tau_le_2 := k4_implies_tau_le_2_if_nu_1 G u v w x h_distinct h_edges h
  linarith

end