/-
Tuza ν ≤ 3: Merged Context File

PROVEN LEMMAS from Aristotle submissions:
- f45bfea3: Core covering machinery (12 lemmas proven)
- 6576c71c: T_e decomposition helpers (4 lemmas proven)

REMAINING TARGETS: tau_Te_le_2_nu_2, tau_Te_le_2_nu_3

KEY INSIGHT: T_e = S_e ∪ (T_e \ S_e) where:
- S_e triangles pairwise share edges → τ(S_e) ≤ 2 (PROVEN)
- T_e \ S_e triangles share edges with BOTH e AND some f ∈ M, f ≠ e
- The 2 edges covering S_e may also cover T_e \ S_e since bridge triangles
  share the same edge with e that S_e triangles do
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Core definitions using triangleEdges and Disjoint
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f))

-- T_e \ S_e: triangles sharing edges with BOTH e AND some other f ∈ M
def T_e_minus_S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ ¬Disjoint (triangleEdges t) (triangleEdges f))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E}

/-! ## Proven Lemmas from f45bfea3 -/

-- Two triangles share an edge iff they share at least 2 vertices
lemma share_edge_iff_inter_ge_2 {V : Type*} [Fintype V] [DecidableEq V]
    (t1 t2 : Finset V) (h1 : t1.card = 3) (h2 : t2.card = 3) :
    ¬Disjoint (triangleEdges t1) (triangleEdges t2) ↔ (t1 ∩ t2).card ≥ 2 := by
      unfold triangleEdges;
      simp +decide [ Finset.disjoint_left, Finset.mem_image ];
      constructor;
      · rintro ⟨ x, u, hu, v, hv, huv, rfl, w, hw, z, hz, hwz, hx ⟩;
        exact Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩;
      · intro h;
        obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 h;
        exact ⟨ _, x, Finset.mem_of_mem_inter_left hx, y, Finset.mem_of_mem_inter_left hy, hxy, rfl, x, Finset.mem_of_mem_inter_right hx, y, Finset.mem_of_mem_inter_right hy, hxy, rfl ⟩

-- If 3 triangles pairwise share edges but don't share a common edge, they fit in 4 vertices
lemma intersecting_triangles_K4_structure_v3 {V : Type*} [Fintype V] [DecidableEq V]
    (t1 t2 t3 : Finset V)
    (h_card : ∀ t ∈ ({t1, t2, t3} : Finset (Finset V)), t.card = 3)
    (h_pair : ∀ t ∈ ({t1, t2, t3} : Finset (Finset V)), ∀ t' ∈ ({t1, t2, t3} : Finset (Finset V)), t ≠ t' → ¬Disjoint (triangleEdges t) (triangleEdges t'))
    (h_no_common : ∀ e : Sym2 V, ¬(e ∈ triangleEdges t1 ∧ e ∈ triangleEdges t2 ∧ e ∈ triangleEdges t3)) :
    ∃ s : Finset V, s.card = 4 ∧ t1 ⊆ s ∧ t2 ⊆ s ∧ t3 ⊆ s := by
      have h_union_ge_4 : (t1 ∪ t2).card = 4 := by
        have h_inter : (t1 ∩ t2).card = 2 := by
          have h_inter_t1_t2 : (t1 ∩ t2).card ≥ 2 := by
            have h_inter_t1_t2 : ¬Disjoint (triangleEdges t1) (triangleEdges t2) := by
              by_cases h : t1 = t2 <;> simp_all +decide;
              simp_all +decide [ Finset.ext_iff, triangleEdges ];
              rcases Finset.card_eq_three.mp h_card.1 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; use Sym2.mk ( x, y ) ; aesop;
            apply (share_edge_iff_inter_ge_2 t1 t2 (h_card t1 (by simp)) (h_card t2 (by simp))).mp h_inter_t1_t2;
          by_cases h : t1 = t2 <;> simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
          · by_cases h : t2 = t3 <;> simp_all +decide;
            · contrapose! h_no_common;
              exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ Sym2.mk ( x, Classical.choose ( Finset.exists_mem_ne ( by linarith ) x ) ), Finset.mem_image.mpr ⟨ ( x, Classical.choose ( Finset.exists_mem_ne ( by linarith ) x ) ), Finset.mem_offDiag.mpr ⟨ hx, Classical.choose_spec ( Finset.exists_mem_ne ( by linarith ) x ) |>.1, Classical.choose_spec ( Finset.exists_mem_ne ( by linarith ) x ) |>.2.symm ⟩, rfl ⟩ ⟩;
            · grind;
          · have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ; );
            interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
            have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
        grind;
      refine' ⟨ _, h_union_ge_4, Finset.subset_union_left, Finset.subset_union_right, _ ⟩;
      have h_inter_t3_t1 : (t3 ∩ t1).card ≥ 2 := by
        have h_inter_t2_t3 : ¬Disjoint (triangleEdges t3) (triangleEdges t1) := by
          by_cases h : t3 = t1 <;> aesop;
        have := share_edge_iff_inter_ge_2 t3 t1 ( h_card t3 ( by simp +decide ) ) ( h_card t1 ( by simp +decide ) ) ; aesop;
      have h_inter_t3_t2 : (t3 ∩ t2).card ≥ 2 := by
        have h_inter_t3_t2 : ¬Disjoint (triangleEdges t3) (triangleEdges t2) := by
          by_cases h : t3 = t2 <;> aesop;
        exact share_edge_iff_inter_ge_2 t3 t2 ( h_card t3 ( by simp +decide ) ) ( h_card t2 ( by simp +decide ) ) |>.1 h_inter_t3_t2;
      have h_inter_t3_t1_t2 : (t3 ∩ (t1 ∪ t2)).card ≥ 3 := by
        have h_inter_t3_t1_t2 : (t3 ∩ (t1 ∪ t2)).card = (t3 ∩ t1).card + (t3 ∩ t2).card - (t3 ∩ t1 ∩ t2).card := by
          rw [ ← Finset.card_union_add_card_inter ];
          simp +decide [ Finset.inter_union_distrib_left, Finset.inter_assoc ];
          simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
        have h_inter_t3_t1_t2 : (t3 ∩ t1 ∩ t2).card ≤ 1 := by
          contrapose! h_no_common;
          obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp h_no_common;
          simp +zetaDelta at *;
          exact ⟨ Sym2.mk ( x, y ), Finset.mem_image.mpr ⟨ ( x, y ), Finset.mem_offDiag.mpr ⟨ hx.2.1, hy.2.1, hxy ⟩, rfl ⟩, Finset.mem_image.mpr ⟨ ( x, y ), Finset.mem_offDiag.mpr ⟨ hx.2.2, hy.2.2, hxy ⟩, rfl ⟩, Finset.mem_image.mpr ⟨ ( x, y ), Finset.mem_offDiag.mpr ⟨ hx.1, hy.1, hxy ⟩, rfl ⟩ ⟩;
        omega;
      have h_inter_t3_t1_t2 : (t3 ∩ (t1 ∪ t2)) = t3 := by
        exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith [ h_card t3 ( by simp +decide ) ] );
      exact h_inter_t3_t1_t2 ▸ Finset.inter_subset_right

-- If two triangles share ≥ 2 edges, they are the same
lemma share_two_edges_implies_same_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (t1 t2 : Finset V) (h1 : t1.card = 3) (h2 : t2.card = 3) :
    (triangleEdges t1 ∩ triangleEdges t2).card ≥ 2 → t1 = t2 := by
      unfold triangleEdges;
      intro h_card
      obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : V, x ≠ y ∧ s(x, y) ∈ Finset.image (fun (x : V × V) => s(x.1, x.2)) t1.offDiag ∩ Finset.image (fun (x : V × V) => s(x.1, x.2)) t2.offDiag ∧ ∃ z w : V, z ≠ w ∧ s(z, w) ∈ Finset.image (fun (x : V × V) => s(x.1, x.2)) t1.offDiag ∩ Finset.image (fun (x : V × V) => s(x.1, x.2)) t2.offDiag ∧ s(x, y) ≠ s(z, w) := by
        have := Finset.one_lt_card.1 h_card;
        rcases this with ⟨ a, ha, b, hb, hab ⟩ ; rcases Finset.mem_image.1 ( Finset.mem_inter.1 ha |>.1 ) with ⟨ x, hx, rfl ⟩ ; rcases Finset.mem_image.1 ( Finset.mem_inter.1 hb |>.1 ) with ⟨ y, hy, rfl ⟩ ; use x.1, x.2, by aesop, by aesop, y.1, y.2, by aesop, by aesop;
      obtain ⟨ z, w, hzw, hzw', h ⟩ := hxy; simp_all +decide [ Finset.ext_iff ] ;
      have h_common_vertices : t1 ∩ t2 ⊇ {x, y, z, w} := by
        simp_all +decide [ Finset.subset_iff ];
        aesop;
      have h_card_common : (t1 ∩ t2).card = 3 := by
        have h_card_common : (t1 ∩ t2).card ≥ 3 := by
          refine' le_trans _ ( Finset.card_mono h_common_vertices );
          grind;
        exact le_antisymm ( le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) h1.le ) h_card_common;
      have h_card_common : (t1 ∩ t2) = t1 ∧ (t1 ∩ t2) = t2 := by
        exact ⟨ Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith ), Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by linarith ) ⟩;
      grind +ring

lemma intersecting_triangles_in_K4_implies_all_in_K4 {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Finset V))
    (h_card : ∀ t ∈ S, t.card = 3)
    (h_pair : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → ¬Disjoint (triangleEdges t1) (triangleEdges t2))
    (s : Finset V) (hs : s.card = 4)
    (t1 t2 t3 : Finset V) (h_in : t1 ∈ S ∧ t2 ∈ S ∧ t3 ∈ S)
    (h_sub : t1 ⊆ s ∧ t2 ⊆ s ∧ t3 ⊆ s)
    (h_no_common : ∀ e : Sym2 V, ¬(e ∈ triangleEdges t1 ∧ e ∈ triangleEdges t2 ∧ e ∈ triangleEdges t3)) :
    ∀ t ∈ S, t ⊆ s := by
      intro t ht
      by_contra h_not_sub
      obtain ⟨x, hx⟩ : ∃ x, x ∈ t ∧ x ∉ s := by
        exact Finset.not_subset.mp h_not_sub;
      have h_inter_ge_2 : (t ∩ t1).card ≥ 2 ∧ (t ∩ t2).card ≥ 2 ∧ (t ∩ t3).card ≥ 2 := by
        have h_inter_ge_2 : ∀ t' ∈ ({t1, t2, t3} : Finset (Finset V)), t ≠ t' → ¬Disjoint (triangleEdges t) (triangleEdges t') := by
          aesop;
        have h_inter_ge_2 : ∀ t' ∈ ({t1, t2, t3} : Finset (Finset V)), t ≠ t' → (t ∩ t').card ≥ 2 := by
          intro t' ht' hne; specialize h_inter_ge_2 t' ht' hne; rw [ share_edge_iff_inter_ge_2 ] at h_inter_ge_2 <;> aesop;
        by_cases h : t = t1 <;> by_cases h' : t = t2 <;> by_cases h'' : t = t3 <;> simp_all +decide;
      have h_inter_s : (t ∩ s).card = 2 := by
        have h_inter_s : (t ∩ s).card ≥ 2 := by
          exact le_trans h_inter_ge_2.1 ( Finset.card_mono fun x hx => by aesop );
        exact le_antisymm ( Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => h_not_sub <| h.symm ▸ Finset.inter_subset_right ⟩ ) ) ( by simp +decide [ * ] ) ) ) h_inter_s;
      obtain ⟨a, b, hab⟩ : ∃ a b : V, a ≠ b ∧ t ∩ s = {a, b} := by
        rw [ Finset.card_eq_two ] at h_inter_s; tauto;
      have h_e_edges : a ∈ t1 ∧ b ∈ t1 ∧ a ∈ t2 ∧ b ∈ t2 ∧ a ∈ t3 ∧ b ∈ t3 := by
        have h_e_edges : (t ∩ t1) ⊆ {a, b} ∧ (t ∩ t2) ⊆ {a, b} ∧ (t ∩ t3) ⊆ {a, b} := by
          grind;
        have := Finset.eq_of_subset_of_card_le h_e_edges.1; have := Finset.eq_of_subset_of_card_le h_e_edges.2.1; have := Finset.eq_of_subset_of_card_le h_e_edges.2.2; simp_all +decide ;
        simp_all +decide [ Finset.ext_iff ];
        grind;
      exact h_no_common ( Sym2.mk ( a, b ) ) ⟨ Finset.mem_image.mpr ⟨ ( a, b ), Finset.mem_offDiag.mpr ⟨ h_e_edges.1, h_e_edges.2.1, by tauto ⟩, rfl ⟩, Finset.mem_image.mpr ⟨ ( a, b ), Finset.mem_offDiag.mpr ⟨ h_e_edges.2.2.1, h_e_edges.2.2.2.1, by tauto ⟩, rfl ⟩, Finset.mem_image.mpr ⟨ ( a, b ), Finset.mem_offDiag.mpr ⟨ h_e_edges.2.2.2.2.1, h_e_edges.2.2.2.2.2, by tauto ⟩, rfl ⟩ ⟩

-- Any family of triangles on 4 vertices can be covered by 2 edges
lemma K4_covering_number {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Finset V))
    (s : Finset V) (hs : s.card = 4)
    (h_sub : ∀ t ∈ S, t ⊆ s)
    (h_card : ∀ t ∈ S, t.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E := by
      obtain ⟨v1, v2, v3, v4, hs_eq⟩ : ∃ v1 v2 v3 v4 : V, s = {v1, v2, v3, v4} ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 := by
        simp_rw +decide [ Finset.card_eq_succ ] at hs ; aesop;
      have h_E_intersects : ∀ t ∈ S, ¬Disjoint (triangleEdges t) {Sym2.mk (v1, v2), Sym2.mk (v3, v4)} := by
        intros t ht
        have h_triangle : t = {v1, v2, v3} ∨ t = {v1, v2, v4} ∨ t = {v1, v3, v4} ∨ t = {v2, v3, v4} := by
          have h_triangle : t ⊆ {v1, v2, v3, v4} ∧ t.card = 3 := by
            aesop;
          rw [ Finset.card_eq_three ] at h_triangle;
          rcases h_triangle with ⟨ ht₁, x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
          rcases ht₁ with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hxy hxz hyz ⊢;
        rcases h_triangle with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ *, triangleEdges ];
      exact ⟨ { Sym2.mk ( v1, v2 ), Sym2.mk ( v3, v4 ) }, Finset.card_insert_le _ _, h_E_intersects ⟩

-- CORE LEMMA: Pairwise edge-sharing triangles can be covered by 2 edges
lemma intersecting_triangles_covering {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Finset V))
    (h_card : ∀ t ∈ S, t.card = 3)
    (h_pair : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → ¬Disjoint (triangleEdges t1) (triangleEdges t2)) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E := by
      by_cases h_card_S : S.card < 2;
      · interval_cases _ : S.card <;> simp_all +decide;
        · exact ⟨ ∅, by norm_num ⟩;
        · obtain ⟨ t, ht ⟩ := Finset.card_eq_one.mp ‹_›;
          obtain ⟨e, he⟩ : ∃ e ∈ triangleEdges t, True := by
            simp +decide [ triangleEdges ];
            rcases Finset.card_eq_three.mp ( h_card t ( ht.symm ▸ Finset.mem_singleton_self _ ) ) with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ), a, b ; aesop;
          exact ⟨ { e }, by simp +decide, by aesop ⟩;
      · obtain ⟨t1, t2, ht1, ht2, h_ne⟩ : ∃ t1 t2 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ t1 ≠ t2 := by
          simpa using Finset.one_lt_card.1 ( by linarith );
        obtain ⟨e, he⟩ : ∃ e : Sym2 V, e ∈ triangleEdges t1 ∧ e ∈ triangleEdges t2 := by
          exact Finset.not_disjoint_iff.mp ( h_pair t1 ht1 t2 ht2 h_ne );
        by_cases h_case_B : ∃ t3 ∈ S, ¬(e ∈ triangleEdges t3);
        · obtain ⟨t3, ht3, h_ne_e⟩ : ∃ t3 ∈ S, ¬(e ∈ triangleEdges t3) := h_case_B;
          have h_no_common : ∀ e' : Sym2 V, ¬(e' ∈ triangleEdges t1 ∧ e' ∈ triangleEdges t2 ∧ e' ∈ triangleEdges t3) := by
            intro e' he'
            have h_eq : t1 = t2 := by
              apply share_two_edges_implies_same_triangle t1 t2 (h_card t1 ht1) (h_card t2 ht2);
              refine' Finset.one_lt_card.2 ⟨ e, _, e', _, _ ⟩ <;> aesop;
            contradiction;
          obtain ⟨s, hs⟩ : ∃ s : Finset V, s.card = 4 ∧ t1 ⊆ s ∧ t2 ⊆ s ∧ t3 ⊆ s := by
            apply intersecting_triangles_K4_structure_v3;
            · aesop;
            · grind;
            · assumption;
          have h_all_in_s : ∀ t ∈ S, t ⊆ s := by
            apply intersecting_triangles_in_K4_implies_all_in_K4 S h_card h_pair s hs.1 t1 t2 t3 ⟨ht1, ht2, ht3⟩ ⟨hs.2.1, hs.2.2.1, hs.2.2.2⟩ h_no_common;
          exact K4_covering_number S s hs.1 h_all_in_s h_card;
        · refine' ⟨ { e }, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ]

-- S_e triangles pairwise share edges (the Lemma 2.2 result)
lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e) (hne : t1 ≠ t2) :
    ¬Disjoint (triangleEdges t1) (triangleEdges t2) := by
  intro h;
  have h_contradiction : IsTrianglePacking G (insert t1 (insert t2 (M \ {e}))) := by
    constructor;
    · have h_subset : t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧ (M \ {e}) ⊆ G.cliqueFinset 3 := by
        exact ⟨ Finset.mem_filter.mp ( Finset.mem_filter.mp ht1 |>.1 ) |>.1, Finset.mem_filter.mp ( Finset.mem_filter.mp ht2 |>.1 ) |>.1, Finset.sdiff_subset.trans ( hM.1.1 ) ⟩;
      exact Finset.insert_subset_iff.mpr ⟨ h_subset.1, Finset.insert_subset_iff.mpr ⟨ h_subset.2.1, h_subset.2.2 ⟩ ⟩;
    · intro x hx y hy hxy;
      simp_all +decide [ S_e ];
      rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> rcases hy with ( rfl | rfl | ⟨ hy, hy' ⟩ ) <;> simp_all +decide [ Function.onFun ];
      · exact h.symm;
      · exact ht1.2 x hx hx' |> Disjoint.symm;
      · exact ht2.2 x hx hx' |> Disjoint.symm;
      · exact hM.1.2 hx hy hxy;
  have h_card : (insert t1 (insert t2 (M \ {e}))).card > M.card := by
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.subset_iff ];
    · grind;
    · intro ht2M; have := hM.1; simp_all +decide [ IsTrianglePacking ] ;
      have := this.2 ht2M he; simp_all +decide [ IsEdgeDisjoint ] ;
      contrapose! this; simp_all +decide [ S_e ] ;
      unfold T_e at ht2; aesop;
    · intro ht1M
      have h_contradiction : ¬Disjoint (triangleEdges t1) (triangleEdges e) := by
        have h_not_disjoint : ¬Disjoint (triangleEdges t1) (triangleEdges e) := by
          have h_filter : t1 ∈ (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f)) := ht1
          unfold T_e at h_filter; aesop;
        exact h_not_disjoint;
      have h_contradiction : IsEdgeDisjoint M := by
        exact hM.1.2;
      have := h_contradiction ht1M he; aesop;
  have h_contradiction : (insert t1 (insert t2 (M \ {e}))).card ≤ packingNumber G := by
    exact le_csSup ⟨ Finset.card ( G.cliqueFinset 3 ), fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact Finset.card_le_card hM.1 ⟩ ⟨ _, rfl, h_contradiction ⟩;
  exact h_card.not_le ( h_contradiction.trans ( hM.2.ge ) )

-- τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain ⟨E, hE_card, hE_inter⟩ : ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ¬Disjoint (triangleEdges t) E := by
    apply intersecting_triangles_covering (S_e G M e) (by
    have h_subset : S_e G M e ⊆ G.cliqueFinset 3 := by
      exact Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _;
    intro t ht; specialize h_subset ht; simp_all +decide ;
    exact h_subset.2) (by
    intro t1 ht1 t2 ht2 hne
    exact S_e_pairwise_share_edges G M hM e he t1 t2 ht1 ht2 hne);
  exact le_trans ( csInf_le' ⟨ E, rfl, hE_inter ⟩ ) hE_card

-- T_e = S_e when ν = 1
lemma Te_eq_Se_when_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    T_e G e = S_e G M e := by
  have hM_eq : M = {e} := by
    rw [ Finset.card_eq_one ] at hnu ; aesop;
  simp [hM_eq, S_e, T_e]

-- τ(T_e) ≤ 2 when ν = 1
lemma tau_Te_le_2_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  have h_tau_T_le_2 : coveringNumberOn G (T_e G e) ≤ coveringNumberOn G (S_e G M e) := by
    rw [ Te_eq_Se_when_nu_1 G M hM hnu e he ];
  exact h_tau_T_le_2.trans ( tau_S_le_2 G M hM e he )

/-! ## Proven Lemmas from 6576c71c (T_e decomposition) -/

-- T_e = S_e ∪ T_e_minus_S_e
lemma T_e_eq_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    T_e G e = S_e G M e ∪ T_e_minus_S_e G M e := by
  ext t
  simp only [Finset.mem_union, S_e, T_e_minus_S_e, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f)
    · left; exact ⟨ht, h⟩
    · right
      push_neg at h
      obtain ⟨f, hfM, hfne, hcard⟩ := h
      exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h
    rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- Triangles in T_e \ S_e share an edge with some f ∈ M, f ≠ e
lemma T_e_minus_S_e_shares_with_other (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V)
    (t : Finset V) (ht : t ∈ T_e_minus_S_e G M e) :
    ∃ f ∈ M, f ≠ e ∧ ¬Disjoint (triangleEdges t) (triangleEdges f) := by
  simp only [T_e_minus_S_e, Finset.mem_filter] at ht
  obtain ⟨_, f, hfM, hfne, hcard⟩ := ht
  exact ⟨f, hfM, hfne, hcard⟩

-- When ν ≤ 3, at most 2 other elements in M besides e
lemma other_packing_elements_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    (M.filter (· ≠ e)).card ≤ 2 := by
  have : (M.filter (· ≠ e)).card = M.card - 1 := by
    rw [Finset.filter_ne']
    simp [Finset.card_erase_of_mem he]
  omega

-- If t shares edge with both e and f, then t ∈ T_e(f)
lemma shared_triangle_coverage (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (t : Finset V) (ht_Te : t ∈ T_e G e) (ht_Tf : ¬Disjoint (triangleEdges t) (triangleEdges f)) :
    t ∈ T_e G f := by
  simp only [T_e, Finset.mem_filter] at ht_Te ⊢
  exact ⟨ht_Te.1, ht_Tf⟩

/-! ## TARGET LEMMAS (remaining sorries) -/

-- τ(T_e) ≤ 2 when ν = 2
lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- τ(T_e) ≤ 2 when ν = 3
lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Combined lemma (depends on nu_2 and nu_3)
lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  rcases Nat.lt_or_eq_of_le hnu with h | h
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h') with h'' | h''
      · -- M.card = 0, impossible since e ∈ M
        simp only [Nat.lt_one_iff] at h''
        exact absurd (Finset.card_pos.mpr ⟨e, he⟩) (by omega)
      · -- M.card = 1
        exact tau_Te_le_2_nu_1 G M hM h'' e he
    · -- M.card = 2
      exact tau_Te_le_2_nu_2 G M hM h' e he
  · -- M.card = 3
    exact tau_Te_le_2_nu_3 G M hM h e he

-- Final theorem (depends on tau_Te_le_2_of_nu_le_3)
theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), IsMaxPacking G M ∧ M.card = packingNumber G := by
    have h_max_packing : ∃ M : Finset (Finset V), M.card = packingNumber G ∧ IsTrianglePacking G M := by
      obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), IsTrianglePacking G M ∧ M.card = packingNumber G := by
        have h_exists_M : ∃ M : Finset (Finset V), IsTrianglePacking G M ∧ M.card = packingNumber G := by
          have h_nonempty : {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}.Nonempty := by
            exact ⟨ 0, ⟨ ∅, rfl, ⟨ Finset.empty_subset _, by simp +decide [ IsEdgeDisjoint ] ⟩ ⟩ ⟩
          have h_finite : {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}.Finite := by
            exact Set.finite_iff_bddAbove.mpr ⟨ Finset.card ( Finset.univ : Finset ( Finset V ) ), fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact Finset.card_le_univ _ ⟩
          generalize_proofs at *;
          have := h_finite.isCompact.sSup_mem h_nonempty; aesop;
        generalize_proofs at *;
        exact h_exists_M;
      exact ⟨ M, hM.2, hM.1 ⟩;
    unfold IsMaxPacking; aesop;
  have h_inter : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ M, ¬Disjoint (triangleEdges t) (triangleEdges e) := by
    intro t ht
    by_contra h_no_inter
    push_neg at h_no_inter
    have hM_plus_t : IsTrianglePacking G (M ∪ {t}) := by
      refine' ⟨ _, _ ⟩ <;> simp_all +decide [ IsTrianglePacking ];
      · have ht_clique : t ∈ G.cliqueFinset 3 := by
          exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ht ⟩;
        exact Finset.insert_subset ht_clique ( hM.1.1.1 );
      · intro x hx y hy hxy; by_cases hx' : x = t <;> by_cases hy' : y = t <;> simp_all +decide ;
        · exact Disjoint.symm ( h_no_inter x hx );
        · exact hM.1.1.2 hx hy hxy |> fun h => by simpa [ triangleEdges ] using h;
    have hM_card_plus_t : (M ∪ {t}).card > M.card := by
      by_cases h : t ∈ M <;> simp_all +decide [ Finset.union_eq_left.2 ];
      specialize h_no_inter t h ; simp_all +decide [ Finset.disjoint_left ] ;
      unfold triangleEdges at h_no_inter; simp_all +decide [ Finset.ext_iff ] ;
      rcases Finset.card_eq_three.mp ht.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; specialize h_no_inter ( Sym2.mk ( x, y ) ) x y ; aesop
    have hM_card_le_packingNumber : (M ∪ {t}).card ≤ packingNumber G := by
      apply le_csSup; exact (by
      exact ⟨ _, fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact Finset.card_le_card hM.1 ⟩); exact ⟨M ∪ {t}, rfl, hM_plus_t⟩;
    have hM_card_le_packingNumber' : M.card < packingNumber G := by
      linarith [hM_card_le_packingNumber]
    exact hM_card_le_packingNumber' |> fun h => by linarith [hM.2] ;
  have h_cover : ∀ e ∈ M, ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) (triangleEdges e) → ¬Disjoint (triangleEdges t) E := by
    intro e he
    have h_cover_e : ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) E := by
      have := tau_Te_le_2_of_nu_le_3 G M hM.1 ( by linarith ) e he
      generalize_proofs at *; (
      contrapose! this; simp_all +decide [ coveringNumberOn ] ;
      refine' lt_of_lt_of_le _ ( le_csInf _ _ );
      exact lt_add_one 2;
      · refine' ⟨ _, ⟨ Finset.univ, rfl, _ ⟩ ⟩ ; simp +decide [ Finset.disjoint_left ];
        simp +decide [ T_e, triangleEdges ];
        exact fun t ht h => by rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ), a, b ; aesop;
      · rintro n ⟨ E, rfl, hE ⟩ ; exact Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => by obtain ⟨ t, ht, ht' ⟩ := this E h; exact ht' |> fun h => hE t ht |> fun h' => h'.elim <| by aesop ) ;)
    generalize_proofs at *; (
    exact ⟨ h_cover_e.choose, h_cover_e.choose_spec.1, fun t ht hte => h_cover_e.choose_spec.2 t <| Finset.mem_filter.mpr ⟨ Finset.mem_coe.mpr ht, hte ⟩ ⟩);
  choose! E hE₁ hE₂ using h_cover;
  have h_union : ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) (Finset.biUnion M E) := by
    intro t ht; obtain ⟨ e, he, he' ⟩ := h_inter t ht; specialize hE₂ e he t ht he'; simp_all +decide [ Finset.disjoint_left ] ;
    exact ⟨ hE₂.choose, hE₂.choose_spec.1, e, he, hE₂.choose_spec.2 ⟩;
  refine' le_trans ( csInf_le _ _ ) _;
  exact ( Finset.biUnion M E ).card;
  · exact ⟨ 0, fun n hn => hn.choose_spec.1.symm ▸ Nat.zero_le _ ⟩;
  · exact ⟨ _, rfl, h_union ⟩;
  · exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm, hM.2 ] using Finset.sum_le_sum hE₁ )

end
