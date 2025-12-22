/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d9a944e6-ef61-4a8c-afa0-597bb286f0b4

The following was proved by Aristotle:

- lemma edge_disjoint_share_le_1 (e f : Finset V)
    (he : e.card = 3) (hf : f.card = 3)
    (h_disjoint : ∀ x y, x ∈ e → y ∈ e → x ≠ y → ∀ a b, a ∈ f → b ∈ f → a ≠ b → ({x, y} : Finset V) ≠ {a, b}) :
    (e ∩ f).card ≤ 1

- lemma bridges_to_f_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (t1 t2 : Finset V) (ht1 : t1 ∈ bridges_to_f G M e f) (ht2 : t2 ∈ bridges_to_f G M e f) :
    (t1 ∩ t2).card ≥ 1

- lemma bridge_count_limit (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (bridges G M e).card ≤ 2 * (M.card - 1)
-/

/-
Tuza ν=4 Portfolio - Slot 4: Bridge Saboteur

TARGET: bridges_limited_by_nu - bridges must be limited or ν increases
STRATEGY: Scaffolded
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def bridges_to_f (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => (t ∩ f).card ≥ 2)

lemma edge_disjoint_share_le_1 (e f : Finset V)
    (he : e.card = 3) (hf : f.card = 3)
    (h_disjoint : ∀ x y, x ∈ e → y ∈ e → x ≠ y → ∀ a b, a ∈ f → b ∈ f → a ≠ b → ({x, y} : Finset V) ≠ {a, b}) :
    (e ∩ f).card ≤ 1 := by
  -- If the intersection had two elements, say x and y, then x and y would be in both e and f. But according to h_disjoint, since x and y are in e and a and b are in f, {x, y} can't equal {a, b}. But if x and y are the same as a and b, that would contradict h_disjoint. Hence, the intersection must have at most one element.
  by_contra h_contra
  have h_two_elements : ∃ x y : V, x ∈ e ∧ y ∈ e ∧ x ≠ y ∧ x ∈ f ∧ y ∈ f := by
    obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp ( not_le.mp h_contra ) ; use x, y; aesop;
  -- Apply the hypothesis `h_disjoint` to the elements `x` and `y` in `e` and `f`.
  obtain ⟨x, y, hx_e, hy_e, hxy, hx_f, hy_f⟩ := h_two_elements;
  specialize h_disjoint x y hx_e hy_e hxy x y hx_f hy_f;
  simp at h_disjoint; -- This should lead to a contradiction because `{x, y}` equals `{x, y}`.;
  -- This contradicts `hxy`, so our assumption that the intersection has more than one element must be false.
  exact hxy h_disjoint

lemma bridges_to_f_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (t1 t2 : Finset V) (ht1 : t1 ∈ bridges_to_f G M e f) (ht2 : t2 ∈ bridges_to_f G M e f) :
    (t1 ∩ t2).card ≥ 1 := by
  -- Since $t1$ and $t2$ are in $bridges_to_f$, they must share the edge $e$.
  have h_common_edge : (t1 ∩ e).card ≥ 2 ∧ (t2 ∩ e).card ≥ 2 := by
    unfold bridges_to_f at ht1 ht2;
    unfold trianglesSharingEdge at ht1 ht2; aesop;
  have h_common_edge : (t1 ∩ e ∩ t2 ∩ e).card ≥ 1 := by
    have h_common_edge : (t1 ∩ e ∩ t2 ∩ e).card ≥ (t1 ∩ e).card + (t2 ∩ e).card - e.card := by
      have h_common_edge : (t1 ∩ e ∩ t2 ∩ e).card ≥ (t1 ∩ e).card + (t2 ∩ e).card - (t1 ∩ e ∪ t2 ∩ e).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
      exact le_trans ( Nat.sub_le_sub_left ( Finset.card_le_card fun x hx => by aesop ) _ ) h_common_edge;
    have := hM.1.1 he; simp_all +decide [ Finset.subset_iff ] ;
    exact Finset.card_pos.mp ( by linarith [ this.card_eq ] );
  exact h_common_edge.trans ( Finset.card_mono fun x hx => by aesop )

/- Aristotle failed to find a proof. -/
lemma bridges_to_f_in_k4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : v ∈ e ∧ v ∈ f) :
    ∃ U : Finset V, U.card ≤ 4 ∧ ∀ t ∈ bridges_to_f G M e f, t ⊆ U := by
  sorry

noncomputable section AristotleLemmas

/-
Decompose the set of bridges into a union of bridges to specific triangles `f`.
-/
lemma bridges_eq_biUnion (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    bridges G M e = (M.erase e).biUnion (fun f => bridges_to_f G M e f) := by
      unfold bridges bridges_to_f; aesop

/-
A combinatorial bound on the number of 2-element subsets of a small set that intersect two disjoint 2-element sets.
-/
lemma combinatorial_helper (U e' f' : Finset V)
    (hU : U.card ≤ 3) (he : e'.card = 2) (hf : f'.card = 2) (hdisj : Disjoint e' f') :
    (U.powerset.filter (fun t => t.card = 2 ∧ (t ∩ e').card ≥ 1 ∧ (t ∩ f').card ≥ 1)).card ≤ 2 := by
      -- Let `x = (e' ∩ U).card` and `y = (f' ∩ U).card`.
      set x := (e' ∩ U).card
      set y := (f' ∩ U).card;
      -- Then any `t ∈ S` has size 2 and intersects both `e'` and `f'`. So `t` is of the form `{u, w}` with `u ∈ e' ∩ U` and `w ∈ f' ∩ U`.
      have hS_subset : Finset.filter (fun t => t.card = 2 ∧ (t ∩ e').card ≥ 1 ∧ (t ∩ f').card ≥ 1) (U.powerset) ⊆ Finset.image (fun p => {p.1, p.2}) (Finset.product (e' ∩ U) (f' ∩ U)) := by
        intro t ht; rw [ Finset.mem_filter ] at ht; rw [ Finset.mem_powerset ] at ht; rcases Finset.card_eq_two.1 ht.2.1 with ⟨ u, v, hu, hv, huv ⟩ ; simp_all +decide [ Finset.disjoint_left ] ;
        rcases ht.2.1 with ⟨ a, ha ⟩ ; rcases ht.2.2 with ⟨ b, hb ⟩ ; use a, b ; simp_all +decide [ Finset.subset_iff ];
        aesop;
      -- Since $x + y \leq 3$ and $x, y \leq 2$, we have $x * y \leq 2$.
      have hxy_le_2 : x * y ≤ 2 := by
        have hxy_le_3 : x + y ≤ 3 := by
          have hxy_le_3 : (e' ∩ U ∪ f' ∩ U).card ≤ 3 := by
            exact le_trans ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_right ) ( Finset.inter_subset_right ) ) ) hU;
          rwa [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx hy => Finset.disjoint_left.mp hdisj ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) ) ] at hxy_le_3;
        cases le_or_gt x 1 <;> cases le_or_gt y 1 <;> nlinarith only [ hxy_le_3, ‹_› ];
      exact le_trans ( Finset.card_le_card hS_subset ) ( Finset.card_image_le.trans ( by erw [ Finset.card_product ] ; exact hxy_le_2 ) )

/-
If there is a bridge between two triangles in a packing, they must share exactly one vertex.
-/
lemma bridges_to_f_inter_card_eq_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_nonempty : (bridges_to_f G M e f).Nonempty) :
    (e ∩ f).card = 1 := by
      obtain ⟨ t, ht ⟩ := h_nonempty;
      -- Since `t` is a bridge between `e` and `f`, we have `(t ∩ e).card ≥ 2` and `(t ∩ f).card ≥ 2`.
      have h_inter_e : (t ∩ e).card ≥ 2 := by
        unfold bridges_to_f at ht;
        unfold trianglesSharingEdge at ht; aesop;
      have h_inter_f : (t ∩ f).card ≥ 2 := by
        unfold bridges_to_f at ht; aesop;
      have h_card_e : e.card = 3 := by
        -- Since $M$ is a packing, each triangle in $M$ must be a clique of size 3.
        have h_clique_size : ∀ t ∈ M, t.card = 3 := by
          have := hM.1.1;
          exact fun t ht => Finset.mem_filter.mp ( this ht ) |>.2.2;
        exact h_clique_size e he
      have h_card_f : f.card = 3 := by
        have := hM.1.1;
        have := this hf; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact this.card_eq
      have h_card_t : t.card = 3 := by
        have h_card_t : t ∈ G.cliqueFinset 3 := by
          exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1;
        exact Finset.mem_filter.mp h_card_t |>.2.2;
      -- Since $M$ is a packing, $e$ and $f$ can only share at most one vertex.
      have h_packing : (e ∩ f).card ≤ 1 := by
        have := hM.1;
        exact this.2 he hf hef;
      -- Since $t$ is a triangle, it must contain exactly 3 vertices.
      have h_t_vertices : (t ∩ e ∩ f).card ≥ 1 := by
        have := Finset.card_union_add_card_inter ( t ∩ e ) ( t ∩ f ) ; simp_all +decide [ Finset.inter_left_comm, Finset.inter_assoc ] ;
        exact Finset.card_pos.mp ( by linarith [ show Finset.card ( t ∩ e ∪ t ∩ f ) ≤ 3 by exact le_trans ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) h_card_t.le ] );
      exact le_antisymm h_packing ( by exact le_trans h_t_vertices ( Finset.card_mono fun x hx => by aesop ) )

/-
Any bridge between two triangles must contain their intersection.
-/
lemma bridges_to_f_subset_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (t : Finset V) (ht : t ∈ bridges_to_f G M e f) :
    e ∩ f ⊆ t := by
      by_contra h_contra;
      -- Let `v` be the unique element of `e ∩ f`.
      obtain ⟨v, hv⟩ : ∃ v, e ∩ f = {v} := by
        have h_card_inter : (e ∩ f).card = 1 := by
          apply bridges_to_f_inter_card_eq_one G M hM e f he hf hef;
          exact ⟨ t, ht ⟩;
        exact Finset.card_eq_one.mp h_card_inter;
      -- Since `t` does not contain `v`, `t ∩ e` and `t ∩ f` are disjoint subsets of `t` each of size at least 2.
      have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
        simp_all +decide [ Finset.disjoint_left ];
        intro a ha₁ ha₂ ha₃; rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop;
      have := Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left : t ∩ e ⊆ t ) ( Finset.inter_subset_left : t ∩ f ⊆ t ) ) ; simp_all +decide ;
      have := Finset.mem_filter.mp ht; simp_all +decide ;
      have := Finset.mem_filter.mp this.1; simp_all +decide ;
      linarith [ this.1.card_eq ]

/-
A combinatorial bound on the number of triangles sharing a vertex and satisfying certain intersection properties.
-/
lemma bridges_counting_bound (S : Finset (Finset V)) (v : V) (U : Finset V) (e f : Finset V)
    (h_subset : ∀ t ∈ S, t ⊆ U)
    (h_inter : ∀ t ∈ S, v ∈ t)
    (h_U_card : U.card ≤ 4)
    (h_e_card : e.card = 3) (h_f_card : f.card = 3)
    (h_v_e : v ∈ e) (h_v_f : v ∈ f)
    (h_disj : Disjoint (e.erase v) (f.erase v))
    (h_t_e : ∀ t ∈ S, (t ∩ e).card ≥ 2)
    (h_t_f : ∀ t ∈ S, (t ∩ f).card ≥ 2)
    (h_t_card : ∀ t ∈ S, t.card = 3) :
    S.card ≤ 2 := by
      by_cases hS : S.Nonempty;
      · -- Let `U' = U.erase v`. Since `v ∈ U` and `U.card ≤ 4`, `U'.card ≤ 3`.
        set U' : Finset V := U.erase v
        have hU'_card : U'.card ≤ 3 := by
          grind;
        -- Let `e' = e.erase v` and `f' = f.erase v`.
        set e' : Finset V := e.erase v
        set f' : Finset V := f.erase v
        have he'_card : e'.card = 2 := by
          rw [ Finset.card_erase_of_mem h_v_e, h_e_card ]
        have hf'_card : f'.card = 2 := by
          rw [ Finset.card_erase_of_mem h_v_f, h_f_card ]
        have he'_disj : Disjoint e' f' := by
          exact h_disj
        have he'_subset : ∀ t ∈ S, (t.erase v) ⊆ U' := by
          exact fun t ht => Finset.subset_iff.mpr fun x hx => Finset.mem_erase_of_ne_of_mem ( by aesop ) ( h_subset t ht ( Finset.mem_of_mem_erase hx ) )
        have he'_card_ge_1 : ∀ t ∈ S, (t.erase v ∩ e').card ≥ 1 := by
          intro t ht; specialize h_t_e t ht; rw [ Finset.inter_comm ] at h_t_e; simp_all +decide [ Finset.card_erase_of_mem ] ;
          obtain ⟨ x, hx ⟩ := Finset.exists_mem_ne h_t_e v; use x; aesop;
        have hf'_card_ge_1 : ∀ t ∈ S, (t.erase v ∩ f').card ≥ 1 := by
          intro t ht
          have h_inter_f : (t ∩ f).card ≥ 2 := h_t_f t ht
          have h_inter_f_erase : (t.erase v ∩ f').card = (t ∩ f).card - 1 := by
            have h_inter_f_erase : (t.erase v ∩ f') = (t ∩ f) \ {v} := by
              ext x; by_cases hx : x = v <;> aesop;
            rw [ h_inter_f_erase, Finset.card_sdiff ] ; aesop;
          exact h_inter_f_erase.symm ▸ Nat.le_sub_one_of_lt h_inter_f
        have ht_card : ∀ t ∈ S, (t.erase v).card = 2 := by
          exact fun t ht => by rw [ Finset.card_erase_of_mem ( h_inter t ht ), h_t_card t ht ] ;
        have hS'_card : (Finset.image (fun t => t.erase v) S).card ≤ (U'.powerset.filter (fun t => t.card = 2 ∧ (t ∩ e').card ≥ 1 ∧ (t ∩ f').card ≥ 1)).card := by
          exact Finset.card_le_card fun x hx => by aesop;
        rw [ Finset.card_image_of_injOn ] at hS'_card;
        · exact hS'_card.trans ( combinatorial_helper U' e' f' hU'_card he'_card hf'_card he'_disj );
        · intro t ht t' ht' h_eq; have := Finset.insert_erase ( h_inter t ht ) ; have := Finset.insert_erase ( h_inter t' ht' ) ; aesop;
      · aesop

/-
The number of bridges between two triangles in a packing is at most 2.
-/
lemma bridges_to_f_card_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (bridges_to_f G M e f).card ≤ 2 := by
      by_cases h_nonempty : (bridges_to_f G M e f).Nonempty;
      · obtain ⟨v, hv⟩ : ∃ v, v ∈ e ∧ v ∈ f := by
          have h_card : (e ∩ f).card = 1 := by
            exact?;
          exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, Finset.mem_of_mem_inter_left hx, Finset.mem_of_mem_inter_right hx ⟩;
        -- By `bridges_to_f_in_k4`, there exists `U` with `U.card ≤ 4` covering `bridges_to_f G M e f`.
        obtain ⟨U, hU_card, hU⟩ : ∃ U : Finset V, U.card ≤ 4 ∧ ∀ t ∈ bridges_to_f G M e f, t ⊆ U := by
          apply bridges_to_f_in_k4 G M hM e f he hf hef v hv;
        apply bridges_counting_bound (bridges_to_f G M e f) v U e f hU (fun t ht => by
          have h_inter : e ∩ f ⊆ t := by
            exact?;
          exact h_inter ( Finset.mem_inter_of_mem hv.1 hv.2 )) hU_card (by
        have := hM.1;
        have := this.1;
        have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact this.2) (by
        have := hM.1.1;
        have := this hf; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact this.2) (by
        exact hv.1) (by
        exact hv.2) (by
        have := hM.1;
        have := this.2;
        specialize this he hf hef ; simp_all +decide [ Finset.disjoint_left ];
        exact fun x hx₁ hx₂ hx₃ => this.not_lt ( Finset.one_lt_card.2 ⟨ x, by aesop, v, by aesop ⟩ )) (by
        intro t ht;
        have := Finset.mem_filter.mp ht;
        unfold trianglesSharingEdge at this; aesop;) (by
        exact fun t ht => Finset.mem_filter.mp ht |>.2 |> fun h => by linarith;) (by
        unfold bridges_to_f;
        simp +decide [ trianglesSharingEdge ];
        exact fun t ht _ _ => ht.card_eq);
      · aesop

end AristotleLemmas

lemma bridge_count_limit (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (bridges G M e).card ≤ 2 * (M.card - 1) := by
  rw [ bridges_eq_biUnion ];
  -- Apply the bound for each bridge to each $f \in M \setminus \{e\}$.
  have h_sum : ∀ f ∈ M.erase e, ((bridges_to_f G M e f).card ≤ 2) := by
    exact fun f hf => bridges_to_f_card_le_2 G M hM e f he ( Finset.mem_of_mem_erase hf ) ( by aesop );
  exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm, Finset.card_erase_of_mem he ] using Finset.sum_le_sum h_sum )

end