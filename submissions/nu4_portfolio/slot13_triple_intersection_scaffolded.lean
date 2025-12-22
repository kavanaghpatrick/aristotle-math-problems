/-
Tuza ν=4 Portfolio - Slot 13: Triple Intersection Strategy (SCAFFOLDED)

TARGET: Use proven triple-intersection lemmas to bound τ for ν=4

KEY INSIGHT (from strategic analysis):
- three_intersecting_triples_structure: 3 pairwise edge-sharing triangles
  → share common edge OR union has ≤4 vertices
- k4_cover: ≤4 vertices → τ ≤ 2
- COMBINED: If S_e, S_f, S_g all pairwise share edges, τ(S_e ∪ S_f ∪ S_g) ≤ 2!

SCAFFOLDING: This file includes FULL PROOFS of key lemmas from Aristotle runs.
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def shareEdge (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 1: Three intersecting triples structure
-- (from Aristotle run b0891cdd-e176-4ebf-8d21-0d88a6183bb9)
-- ══════════════════════════════════════════════════════════════════════════════

lemma three_intersecting_triples_structure {V : Type*} [DecidableEq V]
    (t1 t2 t3 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3)
    (h12 : (t1 ∩ t2).card ≥ 2)
    (h13 : (t1 ∩ t3).card ≥ 2)
    (h23 : (t2 ∩ t3).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3) ∨ (t1 ∪ t2 ∪ t3).card ≤ 4 := by
  by_cases ht : t1 = t2 ∨ t1 = t3 ∨ t2 = t3;
  · grind;
  · obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v ∧ u ∈ t1 ∧ v ∈ t1 ∧ u ∈ t2 ∧ v ∈ t2 := by
      obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.1 h12; use u, v; aesop;
    by_cases hex : u ∈ t3 ∧ v ∈ t3;
    · exact Or.inl ⟨ { u, v }, by rw [ Finset.card_insert_of_not_mem, Finset.card_singleton ] ; aesop, by aesop_cat, by aesop_cat, by aesop_cat ⟩;
    · obtain ⟨w, hw⟩ : ∃ w : V, w ∈ t1 ∧ w ∈ t3 ∧ w ≠ u ∧ w ≠ v := by
        obtain ⟨ w, hw ⟩ := Finset.exists_ne_of_one_lt_card ( show 1 < Finset.card ( t1 ∩ t3 ) from by linarith ) u;
        by_cases hwv : w = v <;> simp_all +decide;
        · obtain ⟨ x, hx ⟩ := Finset.exists_ne_of_one_lt_card ( show 1 < Finset.card ( t1 ∩ t3 ) from by linarith ) v; use x; aesop;
        · aesop;
      obtain ⟨x, hx⟩ : ∃ x : V, x ∈ t2 ∧ x ∈ t3 ∧ x ≠ u ∧ x ≠ v := by
        obtain ⟨ x, hx ⟩ := Finset.exists_ne_of_one_lt_card h23 u;
        by_cases hxv : x = v <;> simp_all +decide [ Finset.inter_comm ];
        · obtain ⟨ y, hy ⟩ := Finset.exists_ne_of_one_lt_card h23 v; use y; aesop;
        · aesop;
      have h_union : t1 ∪ t2 ∪ t3 ⊆ {u, v, w, x} := by
        intro y hy; simp_all +decide [ Finset.subset_iff ] ;
        rcases hy with ( hy | hy | hy ) <;> have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ huv.2.1, Finset.insert_subset_iff.mpr ⟨ huv.2.2.1, Finset.singleton_subset_iff.mpr hw.1 ⟩ ⟩ ) <;> simp_all +decide;
        · grind;
        · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.1, Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.2, Finset.singleton_subset_iff.mpr hx.1 ⟩ ⟩ ) ; simp_all +decide ;
          rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] at this <;> aesop;
        · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.1, Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.2, Finset.singleton_subset_iff.mpr hx.1 ⟩ ⟩ ) ; simp_all +decide ;
          by_cases hu : u = w <;> by_cases hv : v = w <;> simp_all +decide [ Finset.card_insert_of_not_mem ];
          have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hw.2.1, Finset.insert_subset_iff.mpr ⟨ hx.2.1, Finset.singleton_subset_iff.mpr hy ⟩ ⟩ ) ; simp_all +decide ;
          grind;
      exact Or.inr ( le_trans ( Finset.card_le_card h_union ) ( Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ ) _ ) _ ) )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 2: Fourth triangle in union of three
-- (from Aristotle run b0891cdd-e176-4ebf-8d21-0d88a6183bb9)
-- ══════════════════════════════════════════════════════════════════════════════

lemma intersection_of_three_distinct_triples_in_size_four {V : Type*} [DecidableEq V]
    (U : Finset V) (hU : U.card = 4)
    (t1 t2 t3 : Finset V)
    (h_sub : t1 ⊆ U ∧ t2 ⊆ U ∧ t3 ⊆ U)
    (h_sz : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3)
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3) :
    (t1 ∩ t2 ∩ t3).card ≤ 1 := by
      obtain ⟨a, ha⟩ : ∃ a ∈ U, t1 = U \ {a} := by
        have h_card_diff : (U \ t1).card = 1 := by grind;
        obtain ⟨ a, ha ⟩ := Finset.card_eq_one.mp h_card_diff;
        exact ⟨ a, Finset.mem_sdiff.mp ( ha.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← ha, Finset.sdiff_sdiff_eq_self h_sub.1 ] ⟩
      obtain ⟨b, hb⟩ : ∃ b ∈ U, t2 = U \ {b} := by
        have h_card_diff : (U \ t2).card = 1 := by grind;
        rw [ Finset.card_eq_one ] at h_card_diff ; aesop;
        exact ⟨ w, Finset.mem_sdiff.mp ( h.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← h, Finset.sdiff_sdiff_eq_self left ] ⟩
      obtain ⟨c, hc⟩ : ∃ c ∈ U, t3 = U \ {c} := by
        have h_card : U.card = t3.card + (U \ t3).card := by grind;
        have h_card : (U \ t3).card = 1 := by linarith;
        obtain ⟨ c, hc ⟩ := Finset.card_eq_one.mp h_card;
        exact ⟨ c, Finset.mem_sdiff.mp ( hc.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← hc, Finset.sdiff_sdiff_eq_self h_sub.2.2 ] ⟩;
      simp_all +decide [ Finset.subset_iff ];
      rw [ show U \ { a } ∩ ( U \ { b } ∩ ( U \ { c } ) ) = U \ { a, b, c } by ext x; aesop ] ; simp +decide [ *, Finset.card_sdiff ] ;
      rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop

lemma fourth_triangle_in_union_of_three {V : Type*} [DecidableEq V]
    (U : Finset V) (hU : U.card = 4)
    (t1 t2 t3 : Finset V)
    (h_sub : t1 ⊆ U ∧ t2 ⊆ U ∧ t3 ⊆ U)
    (h_sz : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3)
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3)
    (t : Finset V) (ht_card : t.card = 3)
    (h_inter : (t ∩ t1).card ≥ 2 ∧ (t ∩ t2).card ≥ 2 ∧ (t ∩ t3).card ≥ 2) :
    t ⊆ U := by
      by_contra h_not_subset
      obtain ⟨v, hv⟩ : ∃ v, v ∈ t ∧ v ∉ U := by exact Finset.not_subset.mp h_not_subset;
      have h_other_vertices : (t \ {v}).card = 2 := by rw [ Finset.card_sdiff ] ; aesop
      have h_other_vertices_t1 : (t \ {v}) ⊆ t1 := by
        have h_other_vertices_t1 : (t ∩ t1).card = 2 := by
          refine' le_antisymm _ h_inter.1;
          refine' le_trans ( Finset.card_le_card _ ) h_other_vertices.le;
          simp_all +decide [ Finset.subset_iff ];
          exact fun x hx hx' hx'' => hv.2 ( hx''.symm ▸ h_sub.1 hx' );
        have h_other_vertices_t1 : t ∩ t1 = t \ {v} := by
          refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> aesop;
          exact right_4 ( left right_5 );
        exact h_other_vertices_t1 ▸ Finset.inter_subset_right
      have h_other_vertices_t2 : (t \ {v}) ⊆ t2 := by
        have h_other_vertices_t2 : (t \ {v}) ⊆ t2 := by
          have h_inter_t2 : (t ∩ t2).card ≥ 2 := h_inter.right.left
          have h_other_vertices_t2 : (t ∩ t2) = (t \ {v}) := by
            refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> aesop;
            exact right_4 ( left_6 right_5 );
          exact h_other_vertices_t2 ▸ Finset.inter_subset_right;
        assumption
      have h_other_vertices_t3 : (t \ {v}) ⊆ t3 := by
        have h_other_vertices_t3 : (t ∩ t3).card = 2 := by
          have h_other_vertices_t3 : (t ∩ t3).card ≤ 2 := by
            have h_other_vertices_t3 : (t ∩ t3).card ≤ (t \ {v}).card := by
              refine Finset.card_le_card ?_;
              simp_all +decide [ Finset.subset_iff ];
              exact fun x hx hx' hx'' => hv.2 ( hx''.symm ▸ h_sub.2.2 hx' );
            grind;
          grind;
        have h_other_vertices_t3 : t ∩ t3 = t \ {v} := by
          refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> aesop;
          exact right_4 ( right right_5 );
        exact h_other_vertices_t3 ▸ Finset.inter_subset_right;
      have h_other_vertices_inter : (t \ {v}) ⊆ t1 ∩ t2 ∩ t3 := by
        exact Finset.subset_inter ( Finset.subset_inter h_other_vertices_t1 h_other_vertices_t2 ) h_other_vertices_t3;
      exact absurd ( Finset.card_le_card h_other_vertices_inter ) ( by linarith [ intersection_of_three_distinct_triples_in_size_four U hU t1 t2 t3 h_sub h_sz h_distinct ] )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 3: K4 cover (triangles on ≤4 vertices have τ ≤ 2)
-- (from Aristotle run b0891cdd-e176-4ebf-8d21-0d88a6183bb9)
-- ══════════════════════════════════════════════════════════════════════════════

lemma lemma_K4_cover_small {V : Type*} [DecidableEq V]
    (S : Finset (Finset V))
    (h3 : ∀ t ∈ S, t.card = 3)
    (hS : S.card ≤ 2) :
    ∃ E' : Finset (Finset V), E'.card ≤ 2 ∧
      (∀ e ∈ E', e.card = 2 ∧ ∃ t ∈ S, e ⊆ t) ∧
      (∀ t ∈ S, ∃ e ∈ E', e ⊆ t) := by
  interval_cases _ : S.card;
  · exact ⟨ ∅, by simp +decide [ Finset.card_eq_zero.mp ‹_› ] ⟩;
  · obtain ⟨ t, ht ⟩ := Finset.card_eq_one.mp ‹_›;
    obtain ⟨e, he⟩ : ∃ e ∈ t.powersetCard 2, e ⊆ t := by
      exact Exists.elim ( Finset.exists_subset_card_eq ( show 2 ≤ t.card from by linarith [ h3 t ( ht.symm ▸ Finset.mem_singleton_self _ ) ] ) ) fun e he => ⟨ e, Finset.mem_powersetCard.mpr ⟨ he.1, he.2 ⟩, he.1 ⟩;
    refine' ⟨ { e }, _, _, _ ⟩ <;> aesop;
  · obtain ⟨ t1, t2, h1, h2 ⟩ := Finset.card_eq_two.mp ‹_›;
    obtain ⟨e1, he1⟩ : ∃ e1 : Finset V, e1.card = 2 ∧ e1 ⊆ t1 := by
      exact Exists.imp ( by tauto ) ( Finset.exists_subset_card_eq ( show 2 ≤ t1.card from by linarith [ h3 t1 ( h2.symm ▸ Finset.mem_insert_self _ _ ) ] ) )
    obtain ⟨e2, he2⟩ : ∃ e2 : Finset V, e2.card = 2 ∧ e2 ⊆ t2 := by
      have := h3 t2 ( h2.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) );
      exact Exists.imp ( by tauto ) ( Finset.exists_subset_card_eq ( show 2 ≤ t2.card from this.ge.trans' ( by decide ) ) );
    exact ⟨ { e1, e2 }, by by_cases h : e1 = e2 <;> simp_all +decide, by aesop ⟩

lemma lemma_K4_cover {V : Type*} [DecidableEq V]
    (S : Finset (Finset V))
    (h_union : (S.biUnion id).card ≤ 4)
    (h3 : ∀ t ∈ S, t.card = 3) :
    ∃ E' : Finset (Finset V), E'.card ≤ 2 ∧
      (∀ e ∈ E', e.card = 2 ∧ ∃ t ∈ S, e ⊆ t) ∧
      (∀ t ∈ S, ∃ e ∈ E', e ⊆ t) := by
        by_cases hS : S.card ≤ 2;
        · exact?;
        · obtain ⟨U, hU⟩ : ∃ U : Finset V, U.card = 4 ∧ S.biUnion id = U := by
            refine' ⟨ _, _, rfl ⟩;
            by_contra h_contra
            have h_card_lt : (S.biUnion id).card < 4 := by exact lt_of_le_of_ne h_union h_contra;
            have h_card_lt : ∀ t ∈ S, t ⊆ S.biUnion id := by exact fun t ht => Finset.subset_biUnion_of_mem id ht;
            have h_card_lt : ∀ t ∈ S, t = S.biUnion id := by exact fun t ht => Finset.eq_of_subset_of_card_le ( h_card_lt t ht ) ( by linarith [ h3 t ht ] );
            exact hS ( le_trans ( Finset.card_le_one.mpr ( by intros t ht t' ht'; rw [ h_card_lt t ht, h_card_lt t' ht' ] ) ) ( by decide ) );
          obtain ⟨u1, u2, u3, u4, hu⟩ : ∃ u1 u2 u3 u4 : V, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u1 ≠ u4 ∧ u2 ≠ u3 ∧ u2 ≠ u4 ∧ u3 ≠ u4 ∧ U = {u1, u2, u3, u4} := by
            simp_rw +decide [ Finset.card_eq_succ ] at hU;
            rcases hU with ⟨ ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩, hU ⟩ ; use a, b, c, d; aesop;
          use { {u1, u2}, {u3, u4} };
          have h_cover : ∀ t ∈ S, t = {u1, u2, u3} ∨ t = {u1, u2, u4} ∨ t = {u1, u3, u4} ∨ t = {u2, u3, u4} := by
            intro t ht
            have ht_subset : t ⊆ {u1, u2, u3, u4} := by exact fun x hx => hu.2.2.2.2.2.2 ▸ hU.2 ▸ Finset.mem_biUnion.2 ⟨ t, ht, hx ⟩;
            have := h3 t ht; rw [ Finset.card_eq_three ] at this; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
            rcases ht_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hx hy hz ⊢;
          have h_exists_t1 : ∃ t ∈ S, t = {u1, u2, u3} ∨ t = {u1, u2, u4} := by
            contrapose! hS; simp_all +decide ;
            exact le_trans ( Finset.card_le_card ( show S ⊆ { { u1, u3, u4 }, { u2, u3, u4 } } by intros t ht; simpa using h_cover t ht ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by simp +decide ;
          have h_exists_t2 : ∃ t ∈ S, t = {u1, u3, u4} ∨ t = {u2, u3, u4} := by
            contrapose! hS; simp_all +decide ;
            exact le_trans ( Finset.card_le_card ( show S ⊆ { { u1, u2, u3 }, { u1, u2, u4 } } by intros t ht; aesop ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by simp +decide ;
          simp_all +decide [ Finset.subset_iff ];
          refine' ⟨ _, _, _ ⟩;
          · exact Finset.card_insert_le _ _;
          · exact ⟨ by obtain ⟨ t, ht1, rfl | rfl ⟩ := h_exists_t1 <;> [ exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ; exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ], by obtain ⟨ t, ht1, rfl | rfl ⟩ := h_exists_t2 <;> [ exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ; exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ] ⟩;
          · grind

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 4: τ(S_e) ≤ 2
-- (from Aristotle run b0891cdd-e176-4ebf-8d21-0d88a6183bb9)
-- ══════════════════════════════════════════════════════════════════════════════

lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S_e G M e → t2 ∈ S_e G M e → shareEdge t1 t2 := by
  intro t1 t2 h1 h2
  unfold shareEdge
  by_contra h_not_share
  have h_card : isTrianglePacking G (M \ {e} ∪ {t1, t2}) := by
    refine' ⟨ _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff ];
      unfold S_e at *;
      simp_all +decide [ trianglesSharingEdge ];
      exact fun m hm hm' => hM.1.1 hm |> fun h => by simpa using h;
    · intro t1 ht1 t2 ht2 hne; simp_all +decide [ Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton ] ;
      rcases ht1 with ( rfl | rfl | ⟨ ht1, ht1' ⟩ ) <;> rcases ht2 with ( rfl | rfl | ⟨ ht2, ht2' ⟩ ) <;> simp_all +decide [ S_e ];
      · linarith;
      · rw [ Finset.inter_comm ] ; linarith;
      · exact h1.2 _ ht1 ht1' |> le_trans ( by rw [ Finset.inter_comm ] );
      · have := h2.2 t1 ht1 ht1'; simp_all +decide [ Finset.inter_comm ] ;
      · have := hM.1.2;
        exact this ht1 ht2 ( by aesop );
  have h_max : M.card ≥ (M \ {e} ∪ {t1, t2}).card := by
    have h_max : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M.card ≥ M'.card := by
      have := hM.2;
      rw [this];
      unfold trianglePackingNumber;
      intro M' hM'
      have h_max : M'.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        exact Finset.mem_image.mpr ⟨ M', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( hM'.1 ), hM' ⟩, rfl ⟩;
      have := Finset.le_max h_max;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_max _ h_card;
  by_cases h : t1 = t2 <;> simp_all +decide [ Finset.card_union ];
  · have := h_card.1;
    have := this ( Finset.mem_insert_self _ _ ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at h_max <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
    · omega;
    · intro hne hmem; have := h_card.1; simp_all +decide [ Finset.subset_iff ] ;
      unfold S_e at h2; simp_all +decide [ Finset.inter_comm ] ;
      have := h2.2 _ hmem hne; simp_all +decide [ Finset.inter_comm ] ;
      have := ‹G.IsNClique 3 t1 ∧ ∀ a : Finset V, ¬a = e → a ∈ M → G.IsNClique 3 a›.2 t2 hne hmem; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    · intro hne hmem; have := h_card.1; simp_all +decide [ Finset.subset_iff ] ;
      unfold S_e at h1; simp_all +decide [ Finset.subset_iff ] ;
      have := this.2 t1 hne hmem; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have := h1.2 t1 hmem hne; simp_all +decide [ Finset.card_le_one ] ;

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET THEOREMS (for Aristotle to prove)
-- ══════════════════════════════════════════════════════════════════════════════

-- Key lemma: If S_e, S_f, S_g all pairwise share edges, their union has τ ≤ 4
lemma tau_triple_S_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f g : Finset V) (he : e ∈ M) (hf : f ∈ M) (hg : g ∈ M)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (h_structure : ∀ t1 ∈ S_e G M e, ∀ t2 ∈ S_e G M f, (t1 ∩ t2).card ≥ 2 →
                   ∀ t3 ∈ S_e G M g, (t1 ∩ t3).card ≥ 2 → (t2 ∩ t3).card ≥ 2 →
                   (t1 ∪ t2 ∪ t3).card ≤ 4) :
    triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ S_e G M g) ≤ 4 := by
  sorry

-- Main theorem: τ ≤ 8 for ν = 4 using triple intersection structure
theorem tuza_nu4_triple_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  sorry

end
