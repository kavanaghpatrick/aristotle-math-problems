/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e23a4af3-2731-44ce-afb9-8beba495b8ff

The following was proved by Aristotle:

- lemma intersecting_triangles_structure (S : Finset (Finset V))
    (h_nonempty : S.Nonempty)
    (h_card : ∀ t ∈ S, t.card = 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t) ∨
    (∃ A : Finset V, A.card = 4 ∧ ∀ t ∈ S, t ⊆ A)

- lemma pairwise_sharing_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V))
    (hS : S ⊆ G.cliqueFinset 3)
    (hpair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) C

- lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (S_e G M e) ≤ 2

- lemma all_triangles_in_T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hM_ne : M.Nonempty) :
    ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, t ∈ T_e G m

- lemma T_e_minus_S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t : Finset V) (ht : t ∈ T_e G e) (ht_not : t ∉ S_e G M e) :
    ∃ f ∈ M, f ≠ e ∧ sharesEdge t f

- theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G
-/

/-
Tuza's Conjecture: τ(T_e) ≤ 2 for PACKING elements - SCAFFOLDED VERSION

CRITICAL CORRECTION: Previous submission asked about arbitrary triangles.
The flowerGraph counterexample showed τ(T_e) = 3 for the central triangle,
but that triangle is NOT in the maximum packing!

For actual packing elements in flowerGraph:
- M = {{0,1,3}, {1,2,4}, {0,2,5}} with ν = 3
- τ(T_{0,1,3}) = 1, τ(T_{1,2,4}) = 1, τ(T_{0,2,5}) = 1

This version includes helper lemma structure from previous Aristotle runs.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun p => Sym2.mk p)

def sharesEdge (t1 t2 : Finset V) : Prop :=
  ¬Disjoint (triangleEdges t1) (triangleEdges t2)

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M ∧ M.card = trianglePackingNumber G

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => sharesEdge t e)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → ¬sharesEdge t f)

noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : ℕ :=
  (G.edgeFinset.powerset.filter (fun C =>
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) C)).image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  coveringNumberOn G (G.cliqueFinset 3)

-- Helper: Triangles that pairwise share edges form star or K4 structure
noncomputable section AristotleLemmas

/-
If two sets of size 3 intersect in exactly 2 elements, their union has size 4.
-/
lemma card_union_eq_four_of_inter_eq_two {V : Type*} [DecidableEq V] {t₁ t₂ : Finset V} (h₁ : t₁.card = 3) (h₂ : t₂.card = 3) (h_inter : (t₁ ∩ t₂).card = 2) : (t₁ ∪ t₂).card = 4 := by
  have := Finset.card_union_add_card_inter t₁ t₂; aesop;

/-
If t1, t2 intersect in 2 elements, and t3 intersects both in >= 2 elements but is not contained in their union, then t3 must contain the intersection of t1 and t2.
-/
lemma star_center_subset_of_not_subset_union {V : Type*} [DecidableEq V] {t₁ t₂ t₃ : Finset V}
    (h₁ : t₁.card = 3) (h₂ : t₂.card = 3) (h₃ : t₃.card = 3)
    (h₁₂ : (t₁ ∩ t₂).card = 2)
    (h₁₃ : 2 ≤ (t₁ ∩ t₃).card)
    (h₂₃ : 2 ≤ (t₂ ∩ t₃).card)
    (h_not_subset : ¬ t₃ ⊆ t₁ ∪ t₂) :
    t₁ ∩ t₂ ⊆ t₃ := by
      rw [ Finset.card_eq_two ] at h₁₂;
      have := Finset.card_eq_three.mp h₃; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hca ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
      grind

/-
If t is in A, t_outside contains e (subset of A) but is not in A, and t intersects t_outside in >= 2 elements, then t must contain e.
-/
lemma star_center_subset_of_intersect_outside {V : Type*} [DecidableEq V] {A e t t_outside : Finset V}
    (h_e : e.card = 2) (h_t : t.card = 3) (h_outside : t_outside.card = 3)
    (h_e_sub_outside : e ⊆ t_outside)
    (h_e_sub_A : e ⊆ A)
    (h_t_sub_A : t ⊆ A)
    (h_outside_not_sub_A : ¬ t_outside ⊆ A)
    (h_inter : 2 ≤ (t ∩ t_outside).card) :
    e ⊆ t := by
      -- Since e is a subset of A and e is a subset of t_outside, and t_outside is not a subset of A, then e must be a subset of t.
      by_contra h_contra;
      -- Suppose e is not a subset of t. Then their union is exactly {x,y,z} since they cannot be disjoint. This contradicts t_outside not being a subset of A.
      have h_union : (t ∪ t_outside).card = 4 := by
        have := Finset.card_le_card ( Finset.inter_subset_left : t ∩ t_outside ⊆ t ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t ∩ t_outside ⊆ t_outside ) ; ( have := Finset.card_union_add_card_inter t t_outside; simp_all +decide ; ) );
        interval_cases _ : Finset.card ( t ∩ t_outside ) <;> simp_all +decide;
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t ∩ t_outside ⊆ t ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t ∩ t_outside ⊆ t_outside ) ; simp_all +decide ;
      -- Since $e$ is a subset of $t_outside$ and $e$ is not a subset of $t$, the union of $t$ and $t_outside$ must contain all elements of $t$ and $t_outside$, which is 4 elements.
      have h_union_eq : t ∪ t_outside = t ∪ e := by
        have h_union_eq : t ∪ e ⊆ t ∪ t_outside := by
          exact Finset.union_subset_union ( Finset.Subset.refl _ ) h_e_sub_outside;
        rw [ Finset.eq_of_subset_of_card_le h_union_eq ];
        have := Finset.card_union_add_card_inter t e; simp_all +decide ;
        linarith [ show Finset.card ( t ∩ e ) ≤ 1 by exact Nat.le_of_not_lt fun h => h_contra <| Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by linarith ) ▸ Finset.inter_subset_left ];
      have h_union_eq : t_outside ⊆ t ∪ e := by
        exact h_union_eq ▸ Finset.subset_union_right;
      exact h_outside_not_sub_A ( h_union_eq.trans ( Finset.union_subset h_t_sub_A h_e_sub_A ) )

end AristotleLemmas

lemma intersecting_triangles_structure (S : Finset (Finset V))
    (h_nonempty : S.Nonempty)
    (h_card : ∀ t ∈ S, t.card = 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t) ∨
    (∃ A : Finset V, A.card = 4 ∧ ∀ t ∈ S, t ⊆ A) := by
  by_contra h_contra;
  -- If S has at least 2 elements, then we can pick any two distinct triangles t1, t2 in S.
  obtain ⟨t1, ht1, t2, ht2, h_ne⟩ : ∃ t1 ∈ S, ∃ t2 ∈ S, t1 ≠ t2 := by
    rcases S.eq_empty_or_nonempty with ( rfl | ⟨ t, ht ⟩ ) <;> simp_all +decide;
    obtain ⟨ u, hu, htu ⟩ := h_contra.1 ( t.toSet.toFinset.erase ( Classical.choose ( Finset.card_pos.mp ( by linarith [ h_card t ht ] ) ) ) ) ( by
      have := Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ h_card t ht ] ) ) ; aesop; );
    exact ⟨ t, ht, u, hu, by rintro rfl; exact htu <| by simpa using Finset.erase_subset _ _ ⟩;
  -- Let e = t1 ∩ t2 (size 2) and A = t1 ∪ t2 (size 4 by `card_union_eq_four_of_inter_eq_two`).
  set e := t1 ∩ t2
  set A := t1 ∪ t2
  have h_e_card : e.card = 2 := by
    have h_e_card : e.card ≥ 2 ∧ e.card ≤ 3 := by
      exact ⟨ h_pair ht1 ht2 h_ne, le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( h_card t1 ht1 ▸ le_rfl ) ⟩;
    cases h_e_card ; interval_cases _ : Finset.card e <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; aesop;
  have h_A_card : A.card = 4 := by
    have := Finset.card_union_add_card_inter t1 t2; aesop;
  -- Case 2: There exists a triangle t_out in S such that t_out is not a subset of A.
  by_cases h_case2 : ∃ t_out ∈ S, ¬t_out ⊆ A;
  · obtain ⟨t_out, ht_out_S, ht_out_not_subset⟩ : ∃ t_out ∈ S, ¬t_out ⊆ A := h_case2
    have h_star_center : e ⊆ t_out := by
      have h_star_center : 2 ≤ (t1 ∩ t_out).card ∧ 2 ≤ (t2 ∩ t_out).card := by
        aesop;
      apply star_center_subset_of_not_subset_union (h_card t1 ht1) (h_card t2 ht2) (h_card t_out ht_out_S) h_e_card h_star_center.left h_star_center.right ht_out_not_subset
    have h_every_triangle_contains_e : ∀ t ∈ S, e ⊆ t := by
      intro t ht
      by_cases ht_subset_A : t ⊆ A;
      · apply star_center_subset_of_intersect_outside;
        exact h_e_card;
        exact h_card t ht;
        exact h_card t_out ht_out_S;
        exact h_star_center;
        exact Finset.inter_subset_union;
        · exact ht_subset_A;
        · exact ht_out_not_subset;
        · exact h_pair ht ht_out_S ( by aesop );
      · apply star_center_subset_of_not_subset_union (h_card t1 ht1) (h_card t2 ht2) (h_card t ht) h_e_card (by
        exact h_pair ht1 ht ( by aesop )) (by
        exact h_pair ht2 ht ( by aesop )) (by
        exact ht_subset_A)
    exact h_contra (Or.inl ⟨e, h_e_card, h_every_triangle_contains_e⟩);
  · exact h_contra <| Or.inr ⟨ A, h_A_card, fun t ht => Classical.not_not.1 fun h => h_case2 ⟨ t, ht, h ⟩ ⟩

-- Helper: Pairwise sharing implies cover ≤ 2
lemma pairwise_sharing_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V))
    (hS : S ⊆ G.cliqueFinset 3)
    (hpair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) C := by
  by_contra h_contra;
  -- By the lemma intersecting_triangles_structure, S must be contained in a star or a K4.
  have h_structure : (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t) ∨ (∃ A : Finset V, A.card = 4 ∧ ∀ t ∈ S, t ⊆ A) := by
    apply intersecting_triangles_structure S (by
    exact Finset.nonempty_of_ne_empty fun h => h_contra ⟨ ∅, by simp +decide [ h ] ⟩) (by
    intro t ht; specialize hS ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact hS.card_eq) hpair;
  obtain h | h := h_structure;
  · obtain ⟨ e, he ⟩ := h;
    obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp he.1;
    refine' h_contra ⟨ { Sym2.mk ( x, y ) }, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    intro t ht; specialize he t ht; unfold triangleEdges; aesop;
  · obtain ⟨ A, hA₁, hA₂ ⟩ := h;
    -- Since A is a complete graph on 4 vertices, it has 6 edges. We can cover all triangles in S by selecting 2 edges from A.
    have h_cover : ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) C := by
      -- Since A is a complete graph on 4 vertices, it has 6 edges. We can cover all triangles in S by selecting 2 edges from A. Let's denote these edges as e1 and e2.
      obtain ⟨e1, e2, he1, he2⟩ : ∃ e1 e2 : Sym2 V, e1 ≠ e2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) {e1, e2} := by
        -- Since A is a complete graph on 4 vertices, it has 6 edges. We can cover all triangles in S by selecting 2 edges from A. Let's denote these edges as e1 and e2. We need to show that such edges exist.
        obtain ⟨v1, v2, v3, v4, hv⟩ : ∃ v1 v2 v3 v4 : V, v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧ A = {v1, v2, v3, v4} := by
          rcases Finset.card_eq_succ.mp hA₁ with ⟨ v, hv ⟩;
          rcases hv with ⟨ t, ht₁, rfl, ht₂ ⟩ ; rcases Finset.card_eq_three.mp ht₂ with ⟨ w, x, y, hw, hx, hy, h ⟩ ; use v, w, x, y; aesop;
        use Sym2.mk (v1, v2), Sym2.mk (v3, v4);
        simp_all +decide [ Finset.subset_iff, triangleEdges ];
        intro t ht h; have := hS ht; have := Finset.card_eq_three.mp this.2; obtain ⟨ x, y, z, hx, hy, hz, hxyz ⟩ := this; simp_all +decide ;
        have := hA₂ _ ht; simp_all +decide [ Finset.ext_iff ] ;
        grind;
      exact ⟨ { e1, e2 }, by simp +decide [ he1 ], he2 ⟩;
    contradiction

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
-- PROVEN (Parker 2.2): S_e triangles pairwise share edges
lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    (S_e G M e : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card) := by
  sorry

-- PROVEN: τ(S_e) ≤ 2
lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (S_e G M e) ≤ 2 := by
  unfold coveringNumberOn;
  -- By Lemma 2, there exists a covering C of S_e with at most 2 edges.
  obtain ⟨C, hC⟩ : ∃ C : Finset (Sym2 V), C ⊆ G.edgeFinset ∧ C.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ¬Disjoint (triangleEdges t) C := by
    obtain ⟨ C, hC ⟩ := pairwise_sharing_cover_le_2 G ( S_e G M e ) ( by
      exact fun t ht => Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1 ) ( by
      exact S_e_pairwise_share_edges G M hM e he );
    refine' ⟨ C.filter fun x => x ∈ G.edgeFinset, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact le_trans ( Finset.card_filter_le _ _ ) hC.1;
    · simp_all +decide [ Finset.disjoint_left, Set.disjoint_left ];
      intro t ht; obtain ⟨ x, hx₁, hx₂ ⟩ := hC.2 t ht; use x; simp_all +decide [ triangleEdges ] ;
      have := hM.1; simp_all +decide [ S_e ] ;
      have := ht.1; simp_all +decide [ T_e ] ;
      have := ht.1.1.1; aesop;
  have h_min_le_two : (Finset.image Finset.card ({C ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ¬Disjoint (triangleEdges t) C})).min ≤ ↑2 := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ C, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hC.1, hC.2.2 ⟩, rfl ⟩ ) |> le_trans <| Nat.cast_le.mpr hC.2.1;
  cases h : Finset.min ( Finset.image Finset.card ( { C ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ¬Disjoint ( triangleEdges t ) C } ) ) <;> aesop

-- PROVEN: Every triangle shares edge with some packing element
lemma all_triangles_in_T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hM_ne : M.Nonempty) :
    ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, t ∈ T_e G m := by
  intro t ht
  by_contra h_contra
  push_neg at h_contra
  have h_sub : M ∪ {t} ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint := by
    simp_all +decide [ IsMaxPacking, IsEdgeDisjoint ];
    simp_all +decide [ Finset.subset_iff, Set.PairwiseDisjoint ];
    simp_all +decide [ Set.Pairwise, Function.onFun ];
    simp_all +decide [ disjoint_comm, T_e ];
    exact ⟨ fun x hx hx' => by have := h_contra x hx; unfold sharesEdge at this; tauto, fun x hx hx' => by have := h_contra x hx; unfold sharesEdge at this; tauto ⟩;
  have := Finset.le_sup ( f := Finset.card ) h_sub;
  rw [ Finset.union_comm, Finset.card_union_of_disjoint ] at this <;> simp_all +decide [ Finset.disjoint_singleton_right ];
  · obtain ⟨ b, hb₁, hb₂ ⟩ := this; linarith [ hM.2, Finset.card_le_card ( show b ⊆ G.cliqueFinset 3 from hb₁.1 ), show b.card ≤ trianglePackingNumber G from Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hb₁.1, hb₁.2 ⟩ ) ] ;
  · intro h; specialize h_contra t h; simp_all +decide [ T_e ] ;
    unfold sharesEdge at h_contra; simp_all +decide [ Finset.disjoint_left ] ;
    unfold triangleEdges at h_contra; simp_all +decide [ Finset.ext_iff ] ;
    rcases Finset.card_eq_three.mp ht.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; specialize h_contra ( Sym2.mk ( x, y ) ) x y ; aesop

-- KEY: T_e \ S_e structure analysis
-- Triangles in T_e \ S_e share edge with e AND some other f ∈ M
-- For ν ≤ 3, the overlap structure is constrained

lemma T_e_minus_S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t : Finset V) (ht : t ∈ T_e G e) (ht_not : t ∉ S_e G M e) :
    ∃ f ∈ M, f ≠ e ∧ sharesEdge t f := by
  unfold S_e at ht_not; simp_all +decide [ Finset.ext_iff ] ;

/- Aristotle failed to find a proof. -/
-- MAIN: For e in max packing with |M| ≤ 3, τ(T_e) ≤ 2
lemma tau_Te_le_2_for_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- MAIN THEOREM
noncomputable section AristotleLemmas

/-
If there exists a cover C of S with size at most n, then the covering number of S is at most n.
-/
lemma coveringNumberOn_le_of_exists_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (n : ℕ)
    (h : ∃ C ⊆ G.edgeFinset, (∀ t ∈ S, ¬Disjoint (triangleEdges t) C) ∧ C.card ≤ n) :
    coveringNumberOn G S ≤ n := by
      obtain ⟨ C, hC₁, hC₂, hC₃ ⟩ := h;
      -- Since C is a cover of S with size at most n, it must be in the set of covers, and thus the minimal cover's size can't be larger than n.
      have hC_in_covers : C ∈ (G.edgeFinset.powerset.filter (fun C => ∀ t ∈ S, ¬Disjoint (triangleEdges t) C)) := by
        aesop;
      refine' Nat.le_trans _ hC₃;
      unfold coveringNumberOn;
      have hC_in_covers : Finset.min (Finset.image Finset.card (G.edgeFinset.powerset.filter (fun C => ∀ t ∈ S, ¬Disjoint (triangleEdges t) C))) ≤ Finset.card C := by
        exact Finset.min_le ( Finset.mem_image_of_mem _ hC_in_covers );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun C => ∀ t ∈ S, ¬Disjoint ( triangleEdges t ) C ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

/-
The set of all edges in the graph covers any subset of triangles.
-/
lemma edgeFinset_is_cover (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V))
    (hS : S ⊆ G.cliqueFinset 3) :
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) G.edgeFinset := by
      intro t ht
      have h_triangle : t.card = 3 ∧ ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G.Adj u v := by
        have := hS ht; simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.cliqueFinset ] ;
        cases this ; aesop;
      rcases Finset.card_eq_three.mp h_triangle.1 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; simp_all +decide [ Finset.disjoint_left ];
      unfold triangleEdges; aesop;

/-
There exists a subset of edges C that covers S and has cardinality equal to the covering number of S.
-/
lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V))
    (hS : S ⊆ G.cliqueFinset 3) :
    ∃ C ⊆ G.edgeFinset, (∀ t ∈ S, ¬Disjoint (triangleEdges t) C) ∧ C.card = coveringNumberOn G S := by
      unfold coveringNumberOn;
      have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun C ↦ ∀ t ∈ S, ¬Disjoint ( triangleEdges t ) C ) ( Finset.powerset G.edgeFinset ) ) |> Finset.Nonempty ) from ?_ );
      · have := Finset.mem_of_min this.choose_spec;
        rw [ Finset.mem_image ] at this; obtain ⟨ C, hC₁, hC₂ ⟩ := this; use C; aesop;
      · simp +decide [ Finset.Nonempty ];
        exact ⟨ _, G.edgeFinset, ⟨ fun x hx => by simpa using hx, edgeFinset_is_cover G S hS ⟩, rfl ⟩

/-
The covering number is monotonic: if S is a subset of T, then the covering number of S is less than or equal to the covering number of T.
-/
lemma coveringNumberOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) (h : S ⊆ T)
    (hT : T ⊆ G.cliqueFinset 3) :
    coveringNumberOn G S ≤ coveringNumberOn G T := by
      -- Let $C$ be a minimum cover of $T$.
      obtain ⟨C, hC_sub, hC_cover, hC_card⟩ : ∃ C ⊆ G.edgeFinset, (∀ t ∈ T, ¬Disjoint (triangleEdges t) C) ∧ C.card = coveringNumberOn G T := by
        apply exists_min_cover;
        assumption;
      have hC_subset_S : ∀ t ∈ S, ¬Disjoint (triangleEdges t) C := by
        exact fun t ht => hC_cover t ( h ht );
      convert coveringNumberOn_le_of_exists_cover G S _ ⟨ C, hC_sub, hC_subset_S, hC_card.le ⟩ using 1

/-
The covering number of a union of sets of triangles is at most the sum of the covering numbers of the individual sets.
-/
lemma coveringNumberOn_biUnion_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset (Finset V))
    (hf : ∀ i ∈ I, f i ⊆ G.cliqueFinset 3) :
    coveringNumberOn G (I.biUnion f) ≤ ∑ i ∈ I, coveringNumberOn G (f i) := by
      -- Let $C_i$ be a minimum cover for each $f i$.
      obtain ⟨C, hC⟩ : ∃ C : ι → Finset (Sym2 V), (∀ i ∈ I, C i ⊆ G.edgeFinset) ∧ (∀ i ∈ I, ∀ t ∈ f i, ¬Disjoint (triangleEdges t) (C i)) ∧ (∀ i ∈ I, (C i).card = coveringNumberOn G (f i)) := by
        choose! C hC₁ hC₂ hC₃ using fun i hi => exists_min_cover G ( f i ) ( hf i hi );
        use C;
      -- The union of these covers $C_i$ covers the entire union of the $f_i$.
      have h_union_cover : ∀ t ∈ I.biUnion f, ¬Disjoint (triangleEdges t) (Finset.biUnion I C) := by
        simp_all +decide [ Finset.disjoint_left ];
        exact fun t i hi ht => by obtain ⟨ x, hx₁, hx₂ ⟩ := hC.2.1 i hi t ht; exact ⟨ x, hx₁, i, hi, hx₂ ⟩ ;
      -- The cardinality of the union of the covers $C_i$ is at most the sum of their cardinalities.
      have h_card_union : (Finset.biUnion I C).card ≤ ∑ i ∈ I, coveringNumberOn G (f i) := by
        exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun i hi => hC.2.2 i hi ▸ le_rfl );
      refine' le_trans ( coveringNumberOn_le_of_exists_cover _ _ _ _ ) h_card_union;
      exact ⟨ _, Finset.biUnion_subset.2 fun i hi => hC.1 i hi, h_union_cover, le_rfl ⟩

end AristotleLemmas

theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- Let $M$ be a maximum packing. Since $\nu(G) \le 3$, we have $|M| \le 3$.
  obtain ⟨M, hM_max, hM_card⟩ : ∃ M : Finset (Finset V), IsMaxPacking G M ∧ M.card = trianglePackingNumber G := by
    have hM_exists : ∃ M : Finset (Finset V), M ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧ M.card = trianglePackingNumber G := by
      have h_max_packing : ∃ M ∈ Finset.filter IsEdgeDisjoint (G.cliqueFinset 3).powerset, ∀ N ∈ Finset.filter IsEdgeDisjoint (G.cliqueFinset 3).powerset, M.card ≥ N.card := by
        apply_rules [ Finset.exists_max_image ];
        exact ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.empty_subset _, fun _ _ _ => by simp +decide ⟩ ⟩;
      obtain ⟨ M, hM₁, hM₂ ⟩ := h_max_packing;
      exact ⟨ M, hM₁, le_antisymm ( Finset.le_sup ( f := Finset.card ) hM₁ ) ( Finset.sup_le fun N hN => hM₂ N hN ) ⟩;
    unfold IsMaxPacking; aesop;
  -- We know that every triangle in $G$ shares an edge with some triangle in $M$ (Lemma `all_triangles_in_T_e`).
  have h_all_triangles_in_T_e : G.cliqueFinset 3 ⊆ Finset.biUnion M (fun e => T_e G e) := by
    intro t ht
    obtain ⟨e, heM, he⟩ : ∃ e ∈ M, t ∈ T_e G e := by
      apply all_triangles_in_T_e G M hM_max;
      · by_contra hM_empty;
        simp_all +decide [ IsMaxPacking ];
        rw [ eq_comm, trianglePackingNumber ] at hM_card;
        simp_all +decide [ Finset.sup_eq_bot_iff ];
        specialize hM_card { t } ; simp_all +decide [ IsEdgeDisjoint ];
      · exact ht
    aesop;
  -- By monotonicity and subadditivity of the covering number, $\tau(G) \le \sum_{e \in M} \tau(T_e(G, e))$.
  have h_monotone_subadd : coveringNumberOn G (Finset.biUnion M (fun e => T_e G e)) ≤ ∑ e ∈ M, coveringNumberOn G (T_e G e) := by
    apply coveringNumberOn_biUnion_le;
    exact fun e he => Finset.filter_subset _ _;
  refine' le_trans _ ( h_monotone_subadd.trans _ );
  · apply coveringNumberOn_mono;
    · assumption;
    · exact Finset.biUnion_subset.mpr fun e he => Finset.filter_subset _ _;
  · exact le_trans ( Finset.sum_le_sum fun e he => tau_Te_le_2_for_packing G M hM_max ( by linarith ) e he ) ( by simp +decide [ mul_comm, hM_card ] )

end