/-
Tuza τ(S_e) ≤ 2 - FULLY COMPLETE PROOF (NO SORRY)

This file contains all proven lemmas from Aristotle (f9473ebd) plus complete assembly.
ALL PROOFS ARE VERIFIED - ZERO SORRY STATEMENTS.

Key result: tau_S_e_le_2 proves τ(S_e) ≤ 2 for max packing element e.
This is the core lemma for Parker's proof of Tuza's conjecture for ν ≤ 3.

Assembled Dec 2025 with Grok + Gemini assistance.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

def isTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isTriangleCover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def isMaxPacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def shareEdge {V : Type*} [DecidableEq V] (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

noncomputable def triangleCoveringNumberOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

/-
Parker's Lemma 2.2: For max packing M with element e, all triangles in S_e pairwise share edges.
PROVEN by Aristotle (f9473ebd)
-/
lemma lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S_e G e M → t2 ∈ S_e G e M → shareEdge t1 t2 := by
      intros t1 t2 ht1 ht2
      apply Classical.byContradiction
      intro h_contra;
      have h_new_packing : isTrianglePacking G (insert t1 (insert t2 (M.erase e))) := by
        unfold S_e at ht1 ht2;
        simp_all +decide [ isTrianglePacking ];
        unfold trianglesSharingEdge at ht1 ht2; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
        simp_all +decide [ Finset.inter_comm, shareEdge ];
        refine' ⟨ _, _, _, _ ⟩;
        · exact fun a ha ha' => hM.1.1 ha' |> fun h => by simpa using h;
        · exact fun h => Nat.le_of_lt_succ h_contra;
        · exact fun h => Nat.le_of_lt_succ h_contra;
        · have := hM.1.2; aesop;
      have h_card_new_packing : (insert t1 (insert t2 (M.erase e))).card > M.card := by
        rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.ext_iff ];
        · omega;
        · intro x hx h; have := hM.1; simp_all +decide [ isTrianglePacking ] ;
          simp_all +decide [ S_e, Finset.mem_filter ];
          simp_all +decide [ trianglesSharingEdge ];
          have := this.2 h he; simp_all +decide [ Finset.inter_comm ] ;
          exact absurd ( this ( by aesop_cat ) ) ( by linarith );
        · constructor;
          · contrapose! h_contra;
            simp_all +decide [ Finset.ext_iff, shareEdge ];
            have h_card_t1 : t1.card = 3 := by
              have h_card_t1 : t1 ∈ G.cliqueFinset 3 := by
                exact Finset.mem_filter.mp ht1 |>.1 |> Finset.mem_filter.mp |>.1;
              simp_all +decide [ SimpleGraph.cliqueFinset ];
              exact h_card_t1.card_eq;
            rw [ show t1 ∩ t2 = t1 by ext x; aesop ] ; linarith;
          · simp_all +decide [ S_e ];
            intro x hx; intro H; have := ht1.2 _ H; simp_all +decide [ Finset.ext_iff ] ;
            have := this x hx; simp_all +decide [ Finset.card_le_one ] ;
            have := Finset.card_le_one.2 ( fun a ha b hb => this a ha b hb ) ; simp_all +decide [ trianglesSharingEdge ] ;
            exact this.not_lt ( by rw [ ht1.1.1.card_eq ] ; decide );
      have h_contradiction : (insert t1 (insert t2 (M.erase e))).card ≤ trianglePackingNumber G := by
        apply Finset.le_max_of_eq;
        apply Finset.mem_image_of_mem;
        exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_iff.mpr fun x hx => h_new_packing.1 hx ), h_new_packing ⟩;
        unfold trianglePackingNumber;
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        simp_all +decide [ Finset.max ];
        exact h _ ( h_new_packing.1 ) h_new_packing;
      exact h_card_new_packing.not_le ( h_contradiction.trans ( hM.2.ge ) )

/-
If 3 triangles pairwise share edges but don't share a common edge, their union has size 4.
PROVEN by Aristotle (f9473ebd)
-/
lemma lemma_2_1_aux {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 t3 : Finset V) (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) (h3 : t3 ∈ G.cliqueFinset 3)
    (h12 : shareEdge t1 t2) (h13 : shareEdge t1 t3) (h23 : shareEdge t2 t3)
    (h_no_common : ¬∃ u v : V, u ≠ v ∧ {u, v} ⊆ t1 ∧ {u, v} ⊆ t2 ∧ {u, v} ⊆ t3) :
    (t1 ∪ t2 ∪ t3).card = 4 := by
      have h_union : (t1 ∪ t2 ∪ t3).card ≤ 4 := by
        have h_inter_card : (t1 ∩ t2 ∩ t3).card ≤ 1 := by
          contrapose! h_no_common;
          obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h_no_common; use u, v; simp_all +decide [ Finset.subset_iff ] ;
        have h_union_card : (t1 ∪ t2 ∪ t3).card ≤ t1.card + t2.card + t3.card - (t1 ∩ t2).card - (t1 ∩ t3).card - (t2 ∩ t3).card + (t1 ∩ t2 ∩ t3).card := by
          have h_union_card : (t1 ∪ t2 ∪ t3).card = t1.card + t2.card + t3.card - (t1 ∩ t2).card - (t1 ∩ t3).card - (t2 ∩ t3).card + (t1 ∩ t2 ∩ t3).card := by
            rw [ tsub_tsub, tsub_tsub, tsub_add_eq_add_tsub ];
            · rw [ tsub_eq_of_eq_add ];
              have := Finset.card_union_add_card_inter t1 ( t2 ∪ t3 ) ; simp_all +decide [ Finset.inter_union_distrib_left ] ;
              have := Finset.card_union_add_card_inter ( t1 ∩ t2 ) ( t1 ∩ t3 ) ; simp_all +decide [ Finset.inter_left_comm, Finset.inter_comm ] ;
              grind;
            · have h_inter_card : (t1 ∩ t2).card ≤ t1.card ∧ (t1 ∩ t3).card ≤ t1.card ∧ (t2 ∩ t3).card ≤ t2.card := by
                exact ⟨ Finset.card_le_card fun x hx => by aesop, Finset.card_le_card fun x hx => by aesop, Finset.card_le_card fun x hx => by aesop ⟩;
              linarith [ Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t3 ⊆ t1 ), Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t3 ⊆ t3 ) ];
          rw [h_union_card];
        refine le_trans h_union_card ?_;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        unfold shareEdge at *; omega;
      have h_card_ge_3 : (t1 ∪ t2 ∪ t3).card ≥ 3 := by
        have h_card_ge_3 : t1.card ≤ (t1 ∪ t2 ∪ t3).card := by
          exact Finset.card_le_card fun x hx => by aesop;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        exact le_trans ( by rw [ h1.2 ] ) h_card_ge_3;
      interval_cases _ : Finset.card ( t1 ∪ t2 ∪ t3 ) <;> simp_all +decide only;
      have h_subset : t1 ⊆ t1 ∪ t2 ∪ t3 ∧ t2 ⊆ t1 ∪ t2 ∪ t3 ∧ t3 ⊆ t1 ∪ t2 ∪ t3 := by
        grind;
      have h_eq : t1 = t1 ∪ t2 ∪ t3 ∧ t2 = t1 ∪ t2 ∪ t3 ∧ t3 = t1 ∪ t2 ∪ t3 := by
        have h_eq : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3 := by
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact ⟨ h1.2, h2.2, h3.2 ⟩;
        exact ⟨ Finset.eq_of_subset_of_card_le h_subset.1 ( by linarith ), Finset.eq_of_subset_of_card_le h_subset.2.1 ( by linarith ), Finset.eq_of_subset_of_card_le h_subset.2.2 ( by linarith ) ⟩;
      simp_all +singlePass [ shareEdge ];
      obtain ⟨ x, y, z, hxyz ⟩ := Finset.card_eq_three.mp ‹_›;
      exact h_no_common x y hxyz.1 ( by simp +decide [ hxyz.2.2.2 ] )

/-
If a triangle shares an edge with three triangles that form a K4 structure, it is contained in that structure.
PROVEN by Aristotle (f9473ebd)
-/
lemma lemma_2_1_extension {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 t3 t : Finset V) (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) (h3 : t3 ∈ G.cliqueFinset 3) (ht : t ∈ G.cliqueFinset 3)
    (h12 : shareEdge t1 t2) (h13 : shareEdge t1 t3) (h23 : shareEdge t2 t3)
    (h_union : (t1 ∪ t2 ∪ t3).card = 4)
    (h_no_common : ¬∃ u v : V, u ≠ v ∧ {u, v} ⊆ t1 ∧ {u, v} ⊆ t2 ∧ {u, v} ⊆ t3)
    (ht1 : shareEdge t t1) (ht2 : shareEdge t t2) (ht3 : shareEdge t t3) :
    t ⊆ t1 ∪ t2 ∪ t3 := by
      intro x hx; have := ht1; have := ht2; have := ht3; simp_all +decide [ Finset.subset_iff ] ;
      have := Finset.card_eq_three.mp ( show Finset.card t = 3 by exact ht.2 ) ; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; simp_all +decide ;
      rcases hx with ( rfl | rfl | rfl ) <;> simp_all +decide [ shareEdge ] ;
      · grind +ring;
      · grind;
      · grind +ring

/-
Structure of pairwise intersecting triangles: either they all share a common edge, or contained in ≤4 vertices.
PROVEN by Aristotle (f9473ebd)
-/
lemma intersecting_triangles_structure {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3)
    (h_pairwise : Set.Pairwise (T : Set (Finset V)) shareEdge) :
    (∃ u v : V, u ≠ v ∧ ∀ t ∈ T, {u, v} ⊆ t) ∨ (Finset.biUnion T id).card ≤ 4 := by
      by_contra h_contra;
      obtain ⟨t1, t2, ht1, ht2, he⟩ : ∃ t1 t2 : Finset V, t1 ∈ T ∧ t2 ∈ T ∧ t1 ≠ t2 ∧ shareEdge t1 t2 := by
        simp +zetaDelta at *;
        obtain ⟨t1, ht1⟩ : ∃ t1 ∈ T, ∃ t2 ∈ T, t1 ≠ t2 := by
          by_cases h_singleton : T.card = 1;
          · rw [ Finset.card_eq_one ] at h_singleton;
            obtain ⟨ t, rfl ⟩ := h_singleton;
            simp_all +decide [ Finset.subset_iff ];
            exact h_contra.2.not_le ( by rw [ hT.2 ] ; decide );
          · exact Finset.one_lt_card.1 ( lt_of_le_of_ne ( Finset.card_pos.2 ⟨ _, Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ⟩ ) ( Ne.symm h_singleton ) );
        exact ⟨ t1, ht1.1, ht1.2.choose, ht1.2.choose_spec.1, ht1.2.choose_spec.2, h_pairwise ht1.1 ht1.2.choose_spec.1 ht1.2.choose_spec.2 ⟩;
      by_cases h_all_contain_e : ∀ t ∈ T, ∀ u v, u ≠ v → {u, v} ⊆ t1 ∩ t2 → {u, v} ⊆ t;
      · obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : V, u ≠ v ∧ u ∈ t1 ∩ t2 ∧ v ∈ t1 ∩ t2 := by
          exact Exists.imp ( by aesop ) ( Finset.one_lt_card.1 ( lt_of_lt_of_le ( by decide ) he.2 ) );
        exact h_contra <| Or.inl ⟨ u, v, hu, fun t ht => h_all_contain_e t ht u v hu <| by aesop_cat ⟩;
      · obtain ⟨t3, ht3, ht3_not_contain_e⟩ : ∃ t3 : Finset V, t3 ∈ T ∧ ¬∃ u v : V, u ≠ v ∧ {u, v} ⊆ t1 ∩ t2 ∧ {u, v} ⊆ t3 := by
          simp +zetaDelta at *;
          obtain ⟨ t3, ht3, u, v, huv, huv', huv'' ⟩ := h_all_contain_e;
          refine' ⟨ t3, ht3, fun x y hxy hx hy => _ ⟩;
          have hxy_eq_uv : ({x, y} : Finset V) ⊆ t1 ∩ t2 := by
            exact hx;
          have hxy_eq_uv : ({x, y} : Finset V) = t1 ∩ t2 := by
            refine' Finset.eq_of_subset_of_card_le hxy_eq_uv _;
            have := hT ht1; have := hT ht2; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; ( simp_all +decide [ SimpleGraph.isNClique_iff ] ; ) );
            interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
            have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
          grind;
        have h_union_size : (t1 ∪ t2 ∪ t3).card = 4 := by
          apply lemma_2_1_aux G t1 t2 t3 (hT ht1) (hT ht2) (hT ht3) he.right (h_pairwise ht1 ht3 (by
          grind)) (h_pairwise ht2 ht3 (by
          rintro rfl; simp_all +decide [ shareEdge ] ;
          obtain ⟨ x, hx, y, z, hyz, hxy, hxz ⟩ := h_all_contain_e; specialize ht3_not_contain_e y z hyz; simp_all +decide [ Finset.subset_iff ] ;)) (by
          simp_all +decide [ Finset.subset_iff ];
          exact fun x y hxy hx hy hx' hy' hx'' hy'' => ht3_not_contain_e x y hxy hx hx' hy hy' hx'' hy'');
        have h_triangle_in_union : ∀ t ∈ T, shareEdge t t1 ∧ shareEdge t t2 ∧ shareEdge t t3 := by
          intro t ht
          have h_triangle_in_union : shareEdge t t1 ∧ shareEdge t t2 ∧ shareEdge t t3 := by
            have h_triangle_in_union_t1 : shareEdge t t1 := by
              by_cases h : t = t1 <;> simp_all +decide;
              · have := hT ht1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
                have := this.2; simp_all +decide [ Finset.card_eq_three ] ;
                rcases this with ⟨ x, y, hxy, z, hxz, hyz, rfl ⟩ ; simp +decide [ *, shareEdge ] ;
              · exact h_pairwise ht ht1 h
            have h_triangle_in_union_t2 : shareEdge t t2 := by
              by_cases h : t = t2 <;> simp_all +decide [ Set.Pairwise ];
              have := hT ht2; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              exact le_trans ( by simp +decide [ this.2 ] ) ( Finset.card_mono <| show t2 ∩ t2 ⊇ t2 from by simp +decide )
            have h_triangle_in_union_t3 : shareEdge t t3 := by
              cases eq_or_ne t t3 <;> simp_all +decide [ shareEdge ];
              · exact le_trans h_triangle_in_union_t1 ( Finset.card_mono ( Finset.inter_subset_left ) );
              · exact h_pairwise ht ht3 ‹_›
            exact ⟨h_triangle_in_union_t1, h_triangle_in_union_t2, h_triangle_in_union_t3⟩;
          exact h_triangle_in_union;
        have h_triangle_subset_union : ∀ t ∈ T, t ⊆ t1 ∪ t2 ∪ t3 := by
          intros t ht
          apply lemma_2_1_extension G t1 t2 t3 t (hT ht1) (hT ht2) (hT ht3) (hT ht) he.right (by
          grind) (by
          grind) h_union_size (by
          grind) (h_triangle_in_union t ht).left (h_triangle_in_union t ht).right.left (h_triangle_in_union t ht).right.right;
        exact h_contra <| Or.inr <| le_trans ( Finset.card_le_card <| show T.biUnion id ⊆ t1 ∪ t2 ∪ t3 from fun x hx => by rcases Finset.mem_biUnion.mp hx with ⟨ t, ht, hxt ⟩ ; exact h_triangle_subset_union t ht hxt ) h_union_size.le

/-
If all triangles in a set share a common edge, the covering number is at most 1.
PROVEN by Aristotle (f9473ebd)
-/
lemma common_edge_implies_tau_le_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3)
    (u v : V) (huv : u ≠ v) (h_common : ∀ t ∈ T, {u, v} ⊆ t) :
    triangleCoveringNumberOn G T ≤ 1 := by
      unfold triangleCoveringNumberOn
      simp_all +decide;
      refine' Nat.le_of_not_lt fun h => _;
      have h_adj : G.Adj u v := by
        rcases T.eq_empty_or_nonempty with ( rfl | ⟨ t, ht ⟩ ) <;> simp_all +decide [ Finset.subset_iff ];
        · contrapose! h;
          rw [ Finset.min_eq_inf_withTop ];
          rw [ Finset.inf_eq_iInf ];
          exact le_trans ( by erw [ show ( ⨅ a ∈ Finset.image Finset.card G.edgeFinset.powerset, ( a : WithTop ℕ ) ) = 0 from le_antisymm ( by exact ciInf_le_of_le ⟨ 0, Set.forall_mem_range.mpr fun _ => zero_le _ ⟩ 0 <| by aesop ) ( by exact le_ciInf fun _ => by aesop ) ] ) ( by simp +decide );
        · have := hT ht; rw [ SimpleGraph.isNClique_iff ] at this; aesop;
      have h_min : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ T, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ 1 := by
        refine' Finset.min_le _;
        simp;
        exact ⟨ { Sym2.mk ( u, v ) }, ⟨ by aesop_cat, fun t ht => ⟨ Sym2.mk ( u, v ), by aesop_cat ⟩ ⟩, by aesop_cat ⟩;
      contrapose! h;
      cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ T, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop

/-
Any set of triangles on at most 4 vertices can be covered by 2 edges.
PROVEN by Aristotle (f9473ebd)
-/
lemma k4_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.card ≤ 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3 |>.filter (fun t => t ⊆ U)) ≤ 2 := by
      by_cases h_card : U.card ≤ 2;
      · have h_no_triangles : ∀ t ∈ G.cliqueFinset 3, t ⊆ U → False := by
          intro t ht htU; have := Finset.card_le_card htU; simp_all +decide ;
          have := ht.card_eq; interval_cases _ : Finset.card U <;> simp_all +decide ;
        unfold triangleCoveringNumberOn;
        simp +decide [ Finset.min, h_no_triangles ];
        rw [ Finset.inf_eq_iInf ];
        rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
        rotate_left;
        exact 0;
        · exact fun _ => zero_le _;
        · intro w hw;
          refine' ⟨ ∅, _ ⟩ ; aesop;
        · decide +revert;
      · cases hU.eq_or_lt <;> simp_all +decide;
        · have h_triangle_covering : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ (G.cliqueFinset 3).filter (fun x => x ⊆ U), ∃ e ∈ E', e ∈ t.sym2 := by
            have h_triangle_covering : ∃ v1 v2 v3 v4 : V, U = {v1, v2, v3, v4} ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 := by
              simp_rw +decide [ Finset.card_eq_succ ] at *;
              rcases ‹_› with ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ ; use a, b, c, d; aesop;
            obtain ⟨ v1, v2, v3, v4, rfl, h1, h2, h3, h4, h5, h6 ⟩ := h_triangle_covering;
            by_cases h7 : G.Adj v1 v2 <;> by_cases h8 : G.Adj v3 v4 <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
            · refine' ⟨ { Sym2.mk ( v1, v2 ), Sym2.mk ( v3, v4 ) }, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
              intro t ht ht'; have := Finset.card_eq_three.mp ht.2; obtain ⟨ x, y, z, hx, hy, hz, hxyz ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
              grind;
            · refine' ⟨ { Sym2.mk ( v1, v2 ) }, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
              intro t ht ht'; have := Finset.card_eq_three.mp ht.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
              rcases ht' with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp_all +decide;
              all_goals simp_all +decide [ SimpleGraph.isNClique_iff, SimpleGraph.adj_comm ];
            · refine' ⟨ { Sym2.mk ( v3, v4 ) }, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
              intro t ht ht' ht''; have := Finset.card_eq_three.mp ht'; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
              rcases ht'' with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp_all +decide;
              all_goals simp_all +decide [ SimpleGraph.adj_comm ];
            · use ∅; simp +decide [ SimpleGraph.isNClique_iff ] ; aesop;
              rw [ Finset.card_eq_three ] at a_1 ; aesop;
              simp_all +decide [ Finset.subset_iff ];
              rcases a_2 with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp_all ( config := { decide := Bool.true } ) only [ SimpleGraph.adj_comm ] ;
          unfold triangleCoveringNumberOn;
          obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_triangle_covering;
          have h_min_le_two : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ (t : Finset V), G.IsNClique 3 t → t ⊆ U → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ 2 := by
            exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ ) |> le_trans <| by aesop;
          cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, G.IsNClique 3 t → t ⊆ U → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
        · interval_cases _ : U.card ; simp_all +decide [ Finset.subset_iff ];
          have h_empty : {t ∈ G.cliqueFinset 3 | ∀ ⦃x : V⦄, x ∈ t → x ∈ U} = ∅ ∨ {t ∈ G.cliqueFinset 3 | ∀ ⦃x : V⦄, x ∈ t → x ∈ U} = {U} := by
            have h_empty : ∀ t ∈ G.cliqueFinset 3, (∀ ⦃x : V⦄, x ∈ t → x ∈ U) → t = U := by
              intro t ht htU
              have h_card : t.card = 3 := by
                exact Finset.mem_filter.mp ht |>.2.2;
              exact Finset.eq_of_subset_of_card_le htU ( by simp +decide [ * ] );
            exact Classical.or_iff_not_imp_left.2 fun h => Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨ Finset.nonempty_of_ne_empty h, fun t ht => h_empty t ( Finset.mem_filter.mp ht |>.1 ) ( Finset.mem_filter.mp ht |>.2 ) ⟩;
          rcases h_empty with h | h <;> simp +decide [ h, triangleCoveringNumberOn ];
          · simp +decide [ Finset.min ];
            rw [ Finset.inf_eq_iInf ];
            simp +decide [ Option.getD ];
            rw [ show ( ⨅ a : Finset ( Sym2 V ), ⨅ ( _ : ( a : Set ( Sym2 V ) ) ⊆ G.edgeSet ), ( a.card : WithTop ℕ ) ) = 0 from ?_ ] ; simp +decide;
            exact le_antisymm ( ciInf_le_of_le ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩ ∅ <| by simp +decide ) ( zero_le _ );
          · rw [ Finset.eq_singleton_iff_unique_mem ] at h;
            have h_cover : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∃ e ∈ E', ∀ a ∈ e, a ∈ U) ∧ E'.card ≤ 2 := by
              obtain ⟨ u, v, w, h ⟩ := Finset.card_eq_three.mp ‹_›;
              use {Sym2.mk (u, v), Sym2.mk (u, w)};
              simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ];
              have := ‹G.IsNClique 3 { u, v, w } ∧ ∀ x : Finset V, G.IsNClique 3 x → ( ∀ x_1 ∈ x, x_1 = u ∨ x_1 = v ∨ x_1 = w ) → x = { u, v, w } ›.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            obtain ⟨ E', hE'₁, hE'₂, hE'₃ ⟩ := h_cover;
            have h_min : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∃ e ∈ E', ∀ a ∈ e, a ∈ U})).min ≤ 2 := by
              exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'₁, hE'₂ ⟩, rfl ⟩ ) |> le_trans <| by simpa using hE'₃;
            cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∃ e ∈ E', ∀ a ∈ e, a ∈ U ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: Helpers and main theorem
-- ══════════════════════════════════════════════════════════════════════════════

/-
Helper: The full edgeFinset always covers any subset of cliques.
-/
lemma edgeFinset_covers_cliques {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3) :
    G.edgeFinset ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) := by
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro t ht
  have ht_clique := hT ht
  simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_clique
  obtain ⟨hclique, hcard⟩ := ht_clique
  rw [Finset.card_eq_three] at hcard
  obtain ⟨a, b, c, hab, -, -, ht_eq⟩ := hcard
  use s(a, b)
  constructor
  · apply SimpleGraph.mem_edgeFinset.mpr
    apply hclique
    · rw [ht_eq]; simp
    · rw [ht_eq]; simp
    · exact hab
  · rw [ht_eq, Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> simp

/-
Helper: For cliques, covering set is nonempty.
-/
lemma covers_nonempty_of_cliques {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3) :
    (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)).Nonempty :=
  ⟨G.edgeFinset, edgeFinset_covers_cliques G T hT⟩

/-
Helper: Monotonicity of covering number (cover for T works for S ⊆ T)
Proof: if S ⊆ T, any cover for T also covers S.
So {covers for T} ⊆ {covers for S}, hence min over S ≤ min over T.
-/
lemma triangleCoveringNumberOn_mono {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) (hST : S ⊆ T) (hT : T ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G S ≤ triangleCoveringNumberOn G T := by
  unfold triangleCoveringNumberOn
  let coversS := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2)
  let coversT := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)
  have h_sub : coversT ⊆ coversS := fun E' hE' => by
    simp only [coversS, coversT, Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
    exact ⟨hE'.1, fun t ht => hE'.2 t (hST ht)⟩
  have h_img : coversT.image Finset.card ⊆ coversS.image Finset.card := Finset.image_subset_image h_sub
  show (coversS.image Finset.card).min.getD 0 ≤ (coversT.image Finset.card).min.getD 0
  have hT_covers : coversT.Nonempty := covers_nonempty_of_cliques G T hT
  have hT_ne : (coversT.image Finset.card).Nonempty := Finset.Nonempty.image hT_covers _
  have hS_ne : (coversS.image Finset.card).Nonempty := Finset.Nonempty.mono h_img hT_ne
  obtain ⟨minT, hminT⟩ := Finset.min_of_nonempty hT_ne
  obtain ⟨minS, hminS⟩ := Finset.min_of_nonempty hS_ne
  have hminT' : (coversT.image Finset.card).min = some minT := hminT
  have hminS' : (coversS.image Finset.card).min = some minS := hminS
  simp only [hminT', hminS', Option.getD_some]
  have hminT_mem : minT ∈ coversT.image Finset.card := Finset.mem_of_min hminT
  have hminT_in_S : minT ∈ coversS.image Finset.card := h_img hminT_mem
  have h := Finset.min_le hminT_in_S
  rw [hminS] at h
  exact WithTop.coe_le_coe.mp h

-- Helper: S_e is contained in triangles with vertices in biUnion
lemma S_e_subset_filter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    S_e G e M ⊆ (G.cliqueFinset 3).filter (fun t => t ⊆ (S_e G e M).biUnion id) := by
  intro t ht
  simp only [Finset.mem_filter]
  constructor
  · simp only [S_e, trianglesSharingEdge, Finset.mem_filter] at ht
    exact ht.1.1
  · intro v hv
    simp only [Finset.mem_biUnion, id]
    exact ⟨t, ht, hv⟩

-- Helper: S_e ⊆ cliques
lemma S_e_subset_cliques {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    S_e G e M ⊆ G.cliqueFinset 3 := by
  intro t ht
  simp only [S_e, trianglesSharingEdge, Finset.mem_filter] at ht
  exact ht.1.1

/-
THE KEY ASSEMBLY: τ(S_e) ≤ 2

For any max packing M and element e ∈ M, the covering number of S_e is at most 2.
This is the core lemma needed for Parker's proof of Tuza's conjecture for ν ≤ 3.
-/
theorem tau_S_e_le_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  -- S_e triangles pairwise share edges (by lemma_2_2)
  have h_pairwise : Set.Pairwise (S_e G e M : Set (Finset V)) shareEdge := by
    intro t1 ht1 t2 ht2 hne
    exact lemma_2_2 G M hM e he t1 t2 ht1 ht2
  -- S_e ⊆ cliqueFinset 3
  have hS_sub : S_e G e M ⊆ G.cliqueFinset 3 := S_e_subset_cliques G M e
  -- By intersecting_triangles_structure: either common edge or ≤4 vertices
  rcases intersecting_triangles_structure G (S_e G e M) hS_sub h_pairwise with
    ⟨u, v, huv, h_common⟩ | h_small
  -- Case 1: Common edge → τ ≤ 1 ≤ 2
  · calc triangleCoveringNumberOn G (S_e G e M)
        ≤ 1 := common_edge_implies_tau_le_1 G (S_e G e M) hS_sub u v huv h_common
      _ ≤ 2 := by norm_num
  -- Case 2: ≤4 vertices → use k4_cover
  · let U := (S_e G e M).biUnion id
    have hU : U.card ≤ 4 := h_small
    have hT_clique : (G.cliqueFinset 3).filter (fun t => t ⊆ U) ⊆ G.cliqueFinset 3 := Finset.filter_subset _ _
    calc triangleCoveringNumberOn G (S_e G e M)
        ≤ triangleCoveringNumberOn G ((G.cliqueFinset 3).filter (fun t => t ⊆ U)) :=
            triangleCoveringNumberOn_mono G _ _ (S_e_subset_filter G M e) hT_clique
      _ ≤ 2 := k4_cover G U hU

end
