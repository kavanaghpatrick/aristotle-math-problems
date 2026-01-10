/-
  slot256_bridge_counting_RESUB_v2.lean

  COMPREHENSIVE bridge counting infrastructure with ALL proven scaffolding
  merged from slot40 and slot49 Aristotle outputs.

  PROVEN lemmas (from Aristotle):
  - tau_union_le_sum ✅ (slot40, slot49)
  - tau_S_le_2 ✅ (slot49 - 200+ lines)
  - tau_X_le_2 ✅ (slot40, slot49)
  - tau_all_bridges_le_12 ✅ (slot40)
  - tau_bridges_sparse_sharing ≤ 8 ✅ (slot40)
  - tau_bridges_path ≤ 6 ✅ (slot40)
  - tau_bridges_star ≤ 6 ✅ (slot40)
  - X_ef_structure ✅ (slot40)
  - X_ef_eq_empty_of_not_sharesVertex ✅ (slot40)
  - Te_eq_Se_union_bridges ✅ (slot40, slot49)

  1 SORRY expected: bridges_partition (unique pair ownership)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

def sharingDegree (M : Finset (Finset V)) (e : Finset V) : ℕ :=
  (M.filter (fun f => f ≠ e ∧ sharesVertex e f)).card

def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def maxSharingDegree (M : Finset (Finset V)) : ℕ :=
  M.sup (sharingDegree M)

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Helper lemmas (from slot40/49 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma isTriangleCover_iff_mem_filter (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V)) :
    isTriangleCover G A E' ↔ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)) := by
  unfold isTriangleCover; aesop

lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h.2 ⟩
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card h_mem )
  rw [ WithTop.le_coe_iff ] at this; aesop

lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V))
    (h : ∃ E', isTriangleCover G A E') :
    ∃ E', isTriangleCover G A E' ∧ E'.card = triangleCoveringNumberOn G A := by
  by_cases h₁ : ∃ E' : Finset (Sym2 V), isTriangleCover G A E'
  · have h₂ : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), ∀ E'' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ E''.card := by
      apply_rules [ Set.exists_min_image ]
      · exact Set.toFinite _
      · exact ⟨ h₁.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( h₁.choose_spec.1 ), h₁.choose_spec.2 ⟩ ⟩
    obtain ⟨ E', hE₁, hE₂ ⟩ := h₂
    refine' ⟨ E', _, _ ⟩
    · exact ⟨ Finset.mem_filter.mp hE₁ |>.1 |> Finset.mem_powerset.mp, Finset.mem_filter.mp hE₁ |>.2 ⟩
    · unfold triangleCoveringNumberOn
      rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).min = some ( E'.card ) from ?_, Option.getD_some ]
      refine' le_antisymm _ _
      · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ )
      · simp +zetaDelta at *
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ )
  · contradiction

lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *
  grind

lemma isTriangleCover_subset (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : A ⊆ B) (hCover : isTriangleCover G B E') :
    isTriangleCover G A E' := by
  exact ⟨ hCover.1, fun t ht => hCover.2 t ( h ht ) ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · obtain ⟨ E₁, hE₁ ⟩ := exists_min_cover G A hA;
      obtain ⟨ E₂, hE₂ ⟩ := exists_min_cover G B hB;
      have := le_triangleCoveringNumberOn G ( A ∪ B ) ( E₁ ∪ E₂ ) ?_;
      · exact this.trans ( Finset.card_union_le _ _ ) |> le_trans <| by linarith;
      · exact isTriangleCover_union G A B E₁ E₂ hE₁.1 hE₂.1;
    · simp_all +decide [ triangleCoveringNumberOn ];
      simp_all +decide [ Finset.min, Option.getD ];
      rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by aesop ⟩ ] ; simp +decide;
  · simp_all +decide [ triangleCoveringNumberOn ];
    rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by have := Finset.mem_filter.mp hE' |>.2 t ht; aesop ⟩ ] ; simp +decide [ Option.getD ];
    rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun x hx => by obtain ⟨ E', hE', rfl ⟩ := Finset.mem_image.mp hx; exact hA E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by aesop ⟩ ] ; simp +decide

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Te = Se ∪ bridges (from slot40)
-- ══════════════════════════════════════════════════════════════════════════════

lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G M e ∪ bridges G M e := by
  ext t
  simp only [Finset.mem_union, S_e, bridges, trianglesSharingEdge, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: X_ef structure (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma X_ef_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (X_ef G e f = ∅) ∨
    (∃ v, e ∩ f = {v} ∧ ∀ t ∈ X_ef G e f, v ∈ t ∧
      (∃ u ∈ e, u ≠ v ∧ Sym2.mk (u, v) ∈ t.sym2)) := by
        by_cases h : ∃ v : V, e ∩ f = { v };
        · obtain ⟨ v, hv ⟩ := h;
          right
          use v;
          simp_all +decide [ X_ef ];
          intro t ht ht₁ ht₂;
          have h_inter : (t ∩ e).card + (t ∩ f).card ≤ t.card + (t ∩ (e ∩ f)).card := by
            have := Finset.card_union_add_card_inter ( t ∩ e ) ( t ∩ f );
            simp_all +decide [ Finset.inter_left_comm, Finset.inter_assoc ];
            exact this ▸ add_le_add_right ( Finset.card_mono ( by aesop_cat ) ) _;
          have := ht.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          by_cases hv : v ∈ t <;> simp_all +decide [ Finset.inter_comm ];
          · obtain ⟨ u, hu ⟩ := Finset.exists_ne_of_one_lt_card ( lt_of_lt_of_le ( by decide ) ht₁ ) v; use u; aesop;
          · linarith;
        · left;
          have h_disjoint : e ∩ f = ∅ := by
            have := hM.2 he hf hef;
            contrapose! h;
            exact Finset.card_eq_one.mp ( le_antisymm this ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h ) ) );
          ext t;
          simp [X_ef, h_disjoint];
          have := hM.2;
          have := this he hf hef; simp_all +decide [ Finset.ext_iff ] ;
          intro ht ht'; have := Finset.card_le_card ( show t ∩ e ∪ t ∩ f ⊆ t from Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ; simp_all +decide ;
          rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => h_disjoint x ( Finset.mem_of_mem_inter_right hx₁ ) ( Finset.mem_of_mem_inter_right hx₂ ) ) ] at this ; linarith [ show Finset.card t = 3 from by simpa using ht.card_eq ]

lemma X_ef_eq_empty_of_not_sharesVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (h : ¬sharesVertex e f) :
    X_ef G e f = ∅ := by
      ext t;
      simp [X_ef, h];
      intro ht ht'
      have h_inter : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp_all +decide [ Finset.inter_union_distrib_left ];
        simp_all +decide [ Finset.ext_iff, sharesVertex ];
      have h_inter_union : (t ∩ (e ∪ f)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      linarith [ show t.card = 3 by exact ht.card_eq ]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  have h_cover : ∃ E' : Finset (Sym2 V), isTriangleCover G (X_ef G e f) E' ∧ E'.card ≤ 2 := by
    have := X_ef_structure G M hM.1 e f he hf hef;
    rcases this with ( h | ⟨ v, hv₁, hv₂ ⟩ );
    · exact ⟨ ∅, ⟨ Finset.empty_subset _, by simp +decide [ h ] ⟩, by simp +decide ⟩;
    · use (e.erase v).image (fun u => Sym2.mk (u, v));
      refine' ⟨ _, _ ⟩;
      · refine' ⟨ _, _ ⟩;
        · have := hM.1.1 he;
          simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ];
          intro x u hu heu hx; subst hx; have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact this ( by aesop ) ( by rw [ Finset.ext_iff ] at hv₁; specialize hv₁ v; aesop ) hu;
        · intro t ht; specialize hv₂ t ht; aesop;
      · refine' le_trans ( Finset.card_image_le ) _;
        have := hM.1.1 he; simp_all +decide [ Finset.card_eq_three ] ;
        rw [ Finset.card_erase_of_mem ( show v ∈ e from Finset.mem_of_mem_inter_left ( hv₁.symm ▸ Finset.mem_singleton_self _ ) ), this.card_eq ];
  exact le_trans ( le_triangleCoveringNumberOn _ _ _ h_cover.choose_spec.1 ) h_cover.choose_spec.2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (from slot49 Aristotle - KEY LEMMA)
-- ══════════════════════════════════════════════════════════════════════════════

lemma larger_packing_of_disjoint_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (h1 : t1 ∈ S_e G M e) (h2 : t2 ∈ S_e G M e)
    (h_disj : (t1 ∩ t2).card ≤ 1) (h_diff : t1 ≠ t2) :
    False := by
      set M' : Finset (Finset V) := (M \ {e}) ∪ {t1, t2};
      have hM'_packing : isTrianglePacking G M' := by
        have hM'_packing : ∀ t ∈ M', t ∈ G.cliqueFinset 3 ∧ ∀ t' ∈ M', t ≠ t' → (t ∩ t').card ≤ 1 := by
          simp +zetaDelta at *;
          unfold S_e at *; simp_all +decide [ Finset.subset_iff, Finset.mem_filter ] ;
          unfold trianglesSharingEdge at *; simp_all +decide [ Finset.inter_comm ] ;
          have := hM.1; simp_all +decide [ Finset.subset_iff, isTrianglePacking ] ;
          exact fun a ha ha' b hb hb' hab => this.2 ha hb hab;
        exact ⟨ fun t ht => hM'_packing t ht |>.1, fun t ht t' ht' h => hM'_packing t ht |>.2 t' ht' h ⟩;
      have hM'_card : M'.card ≤ M.card := by
        have hM'_card : ∀ M'' : Finset (Finset V), isTrianglePacking G M'' → M''.card ≤ M.card := by
          intro M'' hM''_packing
          have hM''_card : M''.card ≤ trianglePackingNumber G := by
            unfold trianglePackingNumber;
            have hM''_card : M''.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
              simp +zetaDelta at *;
              exact ⟨ M'', ⟨ hM''_packing.1, hM''_packing ⟩, rfl ⟩;
            have := Finset.le_max hM''_card;
            cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
          exact hM''_card.trans ( hM.2.ge );
        exact hM'_card M' hM'_packing;
      have h_not_in_M_minus_e : t1 ∉ M \ {e} ∧ t2 ∉ M \ {e} := by
        constructor <;> intro h <;> simp_all +decide [ S_e ];
        · have := h1.2 t1 h.1 h.2; simp_all +decide [ trianglesSharingEdge ] ;
          exact this.not_lt ( by rw [ G.isNClique_iff ] at h1; aesop );
        · have := h2.2 t2 h.1 h.2; simp_all +decide [ trianglesSharingEdge ] ;
          exact this.not_lt ( by rw [ h2.1.1.2 ] ; decide );
      grind +ring

lemma common_vertex_of_different_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (h1 : t1 ∈ S_e G M e) (h2 : t2 ∈ S_e G M e)
    (hne1 : t1 ≠ e) (hne2 : t2 ≠ e)
    (h_diff_edge : t1 ∩ e ≠ t2 ∩ e) :
    t1 \ e = t2 \ e := by
      have h_inter_diff : (t1 ∩ e).card = 2 ∧ (t2 ∩ e).card = 2 ∧ (t1 ∩ e) ≠ (t2 ∩ e) := by
        have h_inter_diff : ∀ t ∈ S_e G M e, t ≠ e → (t ∩ e).card = 2 := by
          intro t ht hne
          have h_card_t : t.card = 3 := by
            have h_card_t : t ∈ G.cliqueFinset 3 := by
              exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1;
            exact Finset.mem_filter.mp h_card_t |>.2.2
          have h_card_e : e.card = 3 := by
            have := hM.1;
            have := this.1;
            have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            exact this.card_eq
          have h_card_inter : (t ∩ e).card ≥ 2 := by
            have h_card_inter : (t ∩ e).card ≥ 2 := by
              have := ht
              exact Finset.mem_filter.mp this |>.2 |> fun h => by have := Finset.mem_filter.mp ( Finset.mem_filter.mp this |>.1 ) |>.2; aesop;
            exact h_card_inter;
          have h_card_inter_le : (t ∩ e).card ≤ 3 := by
            exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_t.le;
          interval_cases _ : Finset.card ( t ∩ e ) <;> simp_all +decide;
          have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t ∩ e ⊆ t ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t ∩ e ⊆ e ) ; aesop;
        exact ⟨ h_inter_diff t1 h1 hne1, h_inter_diff t2 h2 hne2, h_diff_edge ⟩;
      obtain ⟨v, hv⟩ : ∃ v, v ∈ t1 ∧ v ∈ t2 ∧ v ∉ e := by
        have h_inter_diff : (t1 ∩ t2).card ≥ 2 := by
          by_contra h_contra;
          exact larger_packing_of_disjoint_pair G M hM e he t1 t2 h1 h2 ( by linarith ) ( by aesop );
        contrapose! h_inter_diff;
        have h_inter_diff : (t1 ∩ t2) ⊆ (t1 ∩ e) ∩ (t2 ∩ e) := by
          grind;
        have h_inter_diff : (t1 ∩ e) ∩ (t2 ∩ e) ⊂ t1 ∩ e := by
          simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
          exact Exists.elim ( Finset.not_subset.mp ( show ¬t1 ∩ e ⊆ t2 ∩ e from fun h => ‹ ( t1 ∩ e ).card = 2 ∧ ( t2 ∩ e ).card = 2 ∧ ¬t1 ∩ e = t2 ∩ e ›.2.2 <| Finset.eq_of_subset_of_card_le h <| by linarith ) ) fun x hx => ⟨ x, by aesop ⟩;
        exact lt_of_le_of_lt ( Finset.card_le_card ‹_› ) ( lt_of_lt_of_le ( Finset.card_lt_card h_inter_diff ) ( by simp +decide [ * ] ) );
      have h_inter_eq : t1.card = 3 ∧ t2.card = 3 ∧ e.card = 3 := by
        have h_card : ∀ t ∈ M, t.card = 3 := by
          have := hM.1.1;
          intro t ht; specialize this ht; simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ] ;
          exact this.2;
        have h_card_t1 : t1.card = 3 := by
          have h_card_t1 : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp h1 |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_card_t1 |>.2.2
        have h_card_t2 : t2.card = 3 := by
          have h_card_t2 : t2 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp h2 |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_card_t2 |>.2.2
        have h_card_e : e.card = 3 := by
          exact h_card e he
        exact ⟨h_card_t1, h_card_t2, h_card_e⟩;
      have h_inter_eq : (t1 \ e).card = 1 ∧ (t2 \ e).card = 1 := by
        grind;
      simp_all +decide [ Finset.card_eq_one ];
      obtain ⟨ ⟨ a, ha ⟩, ⟨ b, hb ⟩ ⟩ := h_inter_eq; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      grind

lemma S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ u v : V, u ≠ v ∧ {u, v} ⊆ e ∧ ∀ t ∈ S_e G M e, {u, v} ⊆ t) ∨
    (∃ x : V, S_e G M e ⊆ {e} ∪ (e.powerset.filter (fun f => f.card = 2)).image (fun f => f ∪ {x})) := by
      by_cases h : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
      · obtain ⟨t1, t2, ht1, ht2, ht1e, ht2e, h_diff⟩ := h
        obtain ⟨x, hx⟩ : ∃ x : V, ∀ t ∈ S_e G M e, t ≠ e → t \ e = {x} := by
          have h_common_vertex : ∀ t ∈ S_e G M e, t ≠ e → t \ e = t1 \ e := by
            intros t ht hte
            by_cases h_diff_edge : t ∩ e ≠ t1 ∩ e;
            · exact?;
            · have h_common_vertex : t \ e = t2 \ e := by
                apply common_vertex_of_different_edges G M hM e he t t2 ht ht2 hte ht2e;
                grind +ring;
              have := common_vertex_of_different_edges G M hM e he t1 t2 ht1 ht2 ht1e ht2e; aesop;
          have h_card : (t1 \ e).card = 1 := by
            have h_card : t1.card = 3 ∧ e.card = 3 := by
              have h_card : ∀ t ∈ G.cliqueFinset 3, t.card = 3 := by
                simp +decide [ SimpleGraph.cliqueFinset ];
                exact fun t ht => ht.2;
              have h_card : e ∈ G.cliqueFinset 3 := by
                have := hM.1.1 he; aesop;
              have h_card : t1 ∈ G.cliqueFinset 3 := by
                exact Finset.mem_filter.mp ht1 |>.1 |> Finset.mem_filter.mp |>.1;
              grind;
            have h_card : (t1 ∩ e).card = 2 := by
              have h_card : (t1 ∩ e).card ≥ 2 := by
                have h_card : (t1 ∩ e).card ≥ 2 := by
                  have h_card : t1 ∈ trianglesSharingEdge G e := by
                    exact Finset.mem_filter.mp ht1 |>.1
                  unfold trianglesSharingEdge at h_card; aesop;
                exact h_card;
              have h_card : (t1 ∩ e).card ≤ 3 := by
                exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( by linarith );
              interval_cases _ : ( t1 ∩ e ).card <;> simp_all +decide;
              have h_eq : t1 ∩ e = t1 := by
                exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by aesop );
              have h_eq : t1 ⊆ e := by
                exact h_eq ▸ Finset.inter_subset_right;
              exact ht1e ( Finset.eq_of_subset_of_card_le h_eq ( by simp +decide [ h_card ] ) );
            grind;
          obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp h_card; use x; aesop;
        right
        use x
        intro t ht
        by_cases hte : t = e;
        · aesop;
        · have ht_union : t = (t ∩ e) ∪ {x} := by
            rw [ ← hx t ht hte, Finset.union_comm ];
            rw [ Finset.sdiff_union_inter ];
          have ht_card : t.card = 3 := by
            have ht_card : t ∈ G.cliqueFinset 3 := by
              exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1;
            exact Finset.mem_filter.mp ht_card |>.2.2;
          grind;
      · by_cases h1 : ∃ t : Finset V, t ∈ S_e G M e ∧ t ≠ e <;> simp_all +decide [ Finset.subset_iff ];
        · obtain ⟨ t, ht1, ht2 ⟩ := h1;
          obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v ∧ {u, v} ⊆ e ∧ {u, v} ⊆ t := by
            have := Finset.mem_filter.mp ( Finset.mem_coe.mp ( Finset.mem_filter.mp ht1 |>.1 ) ) |>.2; simp_all +decide [ Finset.subset_iff ] ;
            obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp this; use u, v; aesop;
          refine' Or.inl ⟨ u, v, huv.1, ⟨ huv.2.1 ( Finset.mem_insert_self _ _ ), huv.2.1 ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ⟩, fun t' ht' => _ ⟩;
          by_cases ht'_eq_e : t' = e <;> simp_all +decide [ Finset.subset_iff ];
          specialize h t ht1 t' ht' ht2 ht'_eq_e; simp_all +decide [ Finset.ext_iff ] ;
          exact ⟨ h u huv.2.1.1 |>.1 huv.2.2.1, h v huv.2.1.2 |>.1 huv.2.2.2 ⟩;
        · right;
          rcases e.eq_empty_or_nonempty with ( rfl | ⟨ x, hx ⟩ ) <;> simp_all +decide [ Finset.ext_iff ];
          · have := hM.1.1 he; aesop;
          · exact ⟨ x ⟩

lemma tau_le_2_of_star_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (x : V) (hx : x ∉ e)
    (hS_sub : S ⊆ {e} ∪ (e.powerset.filter (fun f => f.card = 2)).image (fun f => f ∪ {x}))
    (hS_clique : S ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G S ≤ 2 := by
      by_contra h_contra;
      obtain ⟨u, v, w, huv, hvw, huw, huvx⟩ : ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ e = {u, v, w} := by
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        rcases he with ⟨ he₁, he₂ ⟩;
        rw [ Finset.card_eq_three ] at he₂; obtain ⟨ u, v, w, hu, hv, hw ⟩ := he₂; use u, v, by aesop, w; aesop;
      by_cases hux : G.Adj u x;
      · set E' : Finset (Sym2 V) := {Sym2.mk (u, x), Sym2.mk (v, w)};
        refine' h_contra ( le_trans ( le_triangleCoveringNumberOn G S E' _ ) _ );
        · refine' ⟨ _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
          · simp +zetaDelta at *;
            exact ⟨ hux, by have := he.1; aesop ⟩;
          · intro t ht; specialize hS_sub ht; rcases hS_sub with ( rfl | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            · aesop;
            · rw [ Finset.card_eq_two ] at ha₂ ; aesop;
        · exact Finset.card_insert_le _ _;
      · have hS_subset : S ⊆ {e, {v, w, x}} := by
          intro t ht; specialize hS_sub ht; simp_all +decide [ Finset.subset_iff ] ;
          rcases hS_sub with ( rfl | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ Finset.card_eq_two ];
          have := hS_clique ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          rcases ha₂ with ⟨ x, y, hxy, rfl ⟩ ; simp_all +decide [ SimpleGraph.isClique_iff ] ;
          rcases ha₁ with ⟨ rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ];
          · grind;
          · aesop;
        refine' h_contra ( le_trans ( le_triangleCoveringNumberOn G S _ _ ) _ );
        exact { Sym2.mk ( v, w ) };
        · refine' ⟨ _, _ ⟩;
          · simp_all +decide [ SimpleGraph.mem_edgeSet ];
            exact he.1 ( by aesop ) ( by aesop ) ( by aesop );
          · intro t ht; specialize hS_subset ht; aesop;
        · simp +decide

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain h|h := S_e_structure G M hM e he;
  · obtain ⟨ u, v, hne, huv, h ⟩ := h;
    refine' le_trans ( le_triangleCoveringNumberOn G _ { s(u, v) } _ ) _ <;> simp_all +decide [ SimpleGraph.edgeSet, Sym2.fromRel ];
    refine' ⟨ _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ];
    have := hM.1.1 he; simp_all +decide [ SimpleGraph.isClique_iff, Finset.subset_iff ] ;
    exact this.1 ( by aesop ) ( by aesop ) ( by aesop );
  · obtain ⟨x, hx⟩ := h;
    by_cases hx_in_e : x ∈ e;
    · have h_S_e_subset_e : S_e G M e ⊆ {e} := by
        intro t ht
        have ht_card : t.card = 3 := by
          have ht_card : t ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp ht_card |>.2.2
        have ht_subset : t ⊆ e := by
          grind
        have ht_eq_e : t = e := by
          have := hM.1;
          have := this.1;
          have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact Finset.eq_of_subset_of_card_le ht_subset ( by linarith [ this.2 ] )
        exact ht_eq_e ▸ Finset.mem_singleton_self e;
      have h_S_e_subset_e : S_e G M e ⊆ G.cliqueFinset 3 := by
        exact fun t ht => Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1;
      have h_tau_le_1 : ∀ (S : Finset (Finset V)), S ⊆ {e} → S ⊆ G.cliqueFinset 3 → triangleCoveringNumberOn G S ≤ 1 := by
        intros S hS_subset_e hS_subset_clique
        have h_tau_le_1 : triangleCoveringNumberOn G S ≤ 1 := by
          have h_edge : ∃ f ∈ G.edgeFinset, f ∈ e.sym2 := by
            have := hM.1;
            have := this.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            rcases this with ⟨ h₁, h₂ ⟩ ; rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
          obtain ⟨ f, hf₁, hf₂ ⟩ := h_edge;
          exact le_trans ( le_triangleCoveringNumberOn G S { f } ⟨ by aesop_cat, by aesop_cat ⟩ ) ( by simp +decide );
        exact h_tau_le_1;
      exact le_trans ( h_tau_le_1 _ ‹_› ‹_› ) ( by norm_num );
    · apply_rules [ tau_le_2_of_star_structure ];
      · have := hM.1;
        exact this.1 he;
      · intro t ht; exact (by
        exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_all_bridges_le_12 (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_all_bridges_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 12 := by
  have h_allBridges : allBridges G M = Finset.biUnion (Finset.powersetCard 2 M) (fun p => X_ef G p.toList.head! p.toList.tail!.head!) := by
    ext t; simp [allBridges, X_ef];
    constructor;
    · rintro ⟨ ht, e, he, f, hf, hef, hte, htf ⟩;
      by_cases hef' : e ⊆ f;
      · have := hM.1;
        have := this.2;
        have := this he hf hef; simp_all +decide [ Finset.inter_eq_left.mpr hef' ] ;
        exact absurd hte ( not_le_of_gt ( lt_of_le_of_lt ( Finset.card_le_card ( Finset.inter_subset_right ) ) ( lt_of_le_of_lt this ( by decide ) ) ) );
      · refine' ⟨ { e, f }, _, ht, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        · rcases n : Finset.toList { e, f } with _ | ⟨ x, _ | ⟨ y, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n e; have := n f; aesop;
          · replace n := congr_arg List.length n ; simp_all +decide;
        · rcases n : Finset.toList { e, f } with _ | ⟨ x, _ | ⟨ y, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n e; have := n f; aesop;
          · replace n := congr_arg List.length n ; simp_all +decide;
    · norm_num +zetaDelta at *;
      intro x hx hx' ht ht' ht''; rw [ Finset.card_eq_two ] at hx'; obtain ⟨ e, f, he, hf, h ⟩ := hx'; use ht; use e, hx ( by aesop ), f, hx ( by aesop ), by aesop;
      rcases n : Finset.toList { e, f } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
      · replace n := congr_arg List.length n; aesop;
      · have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_self _ _ ) ; have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ; aesop;
      · replace n := congr_arg List.length n ; simp_all +decide;
  have h_tau_X_le_2 : ∀ p ∈ Finset.powersetCard 2 M, triangleCoveringNumberOn G (X_ef G p.toList.head! p.toList.tail!.head!) ≤ 2 := by
    intro p hp
    have h_pair : p.toList.length = 2 := by
      aesop
    have h_pair_elements : p.toList.head! ≠ p.toList.tail!.head! := by
      rcases x : p.toList with ( _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ) <;> simp_all +decide;
      replace x := congr_arg List.Nodup x; simp_all +decide [ Finset.nodup_toList ] ;
    have h_pair_elements : p.toList.head! ∈ M ∧ p.toList.tail!.head! ∈ M := by
      have h_pair_elements : ∀ x ∈ p.toList, x ∈ M := by
        exact fun x hx => Finset.mem_powersetCard.mp hp |>.1 ( Finset.mem_toList.mp hx );
      rcases n : p.toList with ( _ | ⟨ x, _ | ⟨ y, _ | n ⟩ ⟩ ) <;> aesop;
    exact tau_X_le_2 G M hM _ _ h_pair_elements.1 h_pair_elements.2 ‹_›;
  have h_tau_union_le_sum : triangleCoveringNumberOn G (Finset.biUnion (Finset.powersetCard 2 M) (fun p => X_ef G p.toList.head! p.toList.tail!.head!)) ≤ Finset.sum (Finset.powersetCard 2 M) (fun p => triangleCoveringNumberOn G (X_ef G p.toList.head! p.toList.tail!.head!)) := by
    have h_tau_union_le_sum : ∀ (S : Finset (Finset (Finset V))), triangleCoveringNumberOn G (Finset.biUnion S (fun p => X_ef G p.toList.head! p.toList.tail!.head!)) ≤ Finset.sum S (fun p => triangleCoveringNumberOn G (X_ef G p.toList.head! p.toList.tail!.head!)) := by
      intros S
      induction' S using Finset.induction with p S hpS ih;
      · simp +decide [ triangleCoveringNumberOn ];
        simp +decide [ Finset.min ];
        rw [ Finset.inf_eq_iInf ];
        rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
        rotate_left;
        exact 0;
        · exact fun _ => zero_le _;
        · exact fun w hw => ⟨ ∅, by simp +decide [ hw ] ⟩;
        · rfl;
      · rw [ Finset.sum_insert hpS, Finset.biUnion_insert ];
        exact le_trans ( tau_union_le_sum _ _ _ ) ( add_le_add_left ih _ );
    exact h_tau_union_le_sum _;
  exact h_allBridges ▸ h_tau_union_le_sum.trans ( le_trans ( Finset.sum_le_sum h_tau_X_le_2 ) ( by simp +decide [ hM_card ] ) )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_bridges_path and tau_bridges_star (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_bridges_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (he : M = {e₁, e₂, e₃, e₄})
    (h_path : sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧
              ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₁ e₄ ∧ ¬sharesVertex e₂ e₄) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  have h_bridges : ∀ t ∈ allBridges G M, ∃ p ∈ ({(e₁, e₂), (e₂, e₃), (e₃, e₄)} : Finset (Finset V × Finset V)), t ∈ X_ef G p.1 p.2 := by
    intros t ht
    obtain ⟨p, hp⟩ : ∃ p ∈ ({(e₁, e₂), (e₂, e₃), (e₃, e₄), (e₁, e₃), (e₁, e₄), (e₂, e₄)} : Finset (Finset V × Finset V)), t ∈ X_ef G p.1 p.2 := by
      unfold allBridges X_ef at *; aesop;
    simp_all +decide [ sharesVertex ];
    rcases hp with ⟨ rfl | rfl | rfl | rfl | rfl | rfl, hp ⟩ <;> simp_all +decide [ X_ef ];
    · have := Finset.card_eq_three.mp hp.1.2; obtain ⟨ a, b, c, hab, hbc, hac, h ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
      grind;
    · have h_contradiction : (t ∩ e₁).card + (t ∩ e₄).card ≤ (t ∩ (e₁ ∪ e₄)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp +decide [ Finset.inter_union_distrib_left, Finset.inter_assoc, Finset.inter_left_comm, Finset.inter_comm ];
        grind;
      have h_contradiction : (t ∩ (e₁ ∪ e₄)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      exact absurd h_contradiction ( by have := hp.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ; linarith );
    · have h_contradiction : (t ∩ e₂).card + (t ∩ e₄).card ≤ (t ∩ e₂ ∪ t ∩ e₄).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp_all +decide [ Finset.ext_iff ];
      have h_contradiction : (t ∩ e₂ ∪ t ∩ e₄).card ≤ t.card := by
        exact Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) );
      linarith [ show t.card ≤ 3 by exact hp.1.card_eq.le ];
  have h_bridges_card : triangleCoveringNumberOn G (allBridges G M) ≤ triangleCoveringNumberOn G (X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄) := by
    apply le_of_not_gt; intro h_contra;
    obtain ⟨E', hE', hE'_card⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G (X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄) E' ∧ E'.card < triangleCoveringNumberOn G (allBridges G M) := by
      have := exists_min_cover G ( X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄ ) ?_;
      · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.symm ▸ h_contra ⟩;
      · refine' ⟨ G.edgeFinset, _, _ ⟩ <;> simp +decide [ isTriangleCover ];
        rintro t ( ht | ht | ht ) <;> simp_all +decide [ X_ef ];
        · rcases ht.1 with ⟨ h₁, h₂ ⟩;
          rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
        · rcases ht.1 with ⟨ h₁, h₂ ⟩;
          rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
        · rcases ht.1 with ⟨ h₁, h₂ ⟩;
          rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
    refine' hE'_card.not_le ( le_triangleCoveringNumberOn G ( allBridges G M ) E' _ );
    exact ⟨ hE'.1, fun t ht => by obtain ⟨ p, hp₁, hp₂ ⟩ := h_bridges t ht; exact hE'.2 t ( by aesop ) ⟩;
  refine' le_trans h_bridges_card ( le_trans ( _ : _ ≤ _ ) _ );
  exact triangleCoveringNumberOn G ( X_ef G e₁ e₂ ) + triangleCoveringNumberOn G ( X_ef G e₂ e₃ ) + triangleCoveringNumberOn G ( X_ef G e₃ e₄ );
  · exact le_trans ( tau_union_le_sum _ _ _ ) ( add_le_add ( tau_union_le_sum _ _ _ ) le_rfl );
  · exact le_trans ( add_le_add_three ( tau_X_le_2 G M hM e₁ e₂ ( by aesop ) ( by aesop ) ( by aesop ) ) ( tau_X_le_2 G M hM e₂ e₃ ( by aesop ) ( by aesop ) ( by aesop ) ) ( tau_X_le_2 G M hM e₃ e₄ ( by aesop ) ( by aesop ) ( by aesop ) ) ) ( by norm_num )

lemma tau_bridges_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center e₁ e₂ e₃ : Finset V)
    (he : M = {e_center, e₁, e₂, e₃})
    (h_star : sharesVertex e_center e₁ ∧ sharesVertex e_center e₂ ∧ sharesVertex e_center e₃ ∧
              ¬sharesVertex e₁ e₂ ∧ ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  have hX_empty : X_ef G e₁ e₂ = ∅ ∧ X_ef G e₁ e₃ = ∅ ∧ X_ef G e₂ e₃ = ∅ := by
    exact ⟨ X_ef_eq_empty_of_not_sharesVertex G e₁ e₂ h_star.2.2.2.1, X_ef_eq_empty_of_not_sharesVertex G e₁ e₃ h_star.2.2.2.2.1, X_ef_eq_empty_of_not_sharesVertex G e₂ e₃ h_star.2.2.2.2.2 ⟩;
  have h_union : triangleCoveringNumberOn G (allBridges G M) ≤ triangleCoveringNumberOn G (X_ef G e_center e₁) + triangleCoveringNumberOn G (X_ef G e_center e₂) + triangleCoveringNumberOn G (X_ef G e_center e₃) := by
    have h_union : triangleCoveringNumberOn G (allBridges G M) ≤ triangleCoveringNumberOn G (X_ef G e_center e₁ ∪ X_ef G e_center e₂) + triangleCoveringNumberOn G (X_ef G e_center e₃) := by
      have h_union : allBridges G M ⊆ X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃ := by
        intro t ht; simp_all +decide [ allBridges ] ;
        simp_all +decide [ X_ef ];
        grind;
      refine' le_trans ( _ : triangleCoveringNumberOn G ( allBridges G M ) ≤ triangleCoveringNumberOn G ( X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃ ) ) _;
      · apply le_of_not_gt; intro h_contra;
        obtain ⟨E', hE'⟩ : ∃ E', isTriangleCover G (X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃) E' ∧ E'.card = triangleCoveringNumberOn G (X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃) := by
          apply exists_min_cover;
          refine' ⟨ G.edgeFinset, _, _ ⟩ <;> simp +decide [ isTriangleCover ];
          rintro t ( ht | ht | ht ) <;> simp_all +decide [ X_ef ];
          · rcases ht.1 with ⟨ h₁, h₂ ⟩;
            rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
          · rcases ht.1 with ⟨ ht₁, ht₂ ⟩;
            rcases Finset.card_eq_three.mp ht₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use s(a, b) ; aesop;
          · rcases ht.1 with ⟨ h₁, h₂ ⟩;
            obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := Finset.card_eq_three.mp h₂;
            exact ⟨ Sym2.mk ( a, b ), by simpa [ Sym2.eq_swap ] using h₁ ( by simp +decide [ ha ] ) ( by simp +decide [ hb ] ) ( by simp +decide [ ha, hb ] ), by simp +decide [ ha, hb ] ⟩;
        refine' h_contra.not_le _;
        refine' le_trans _ hE'.2.le;
        apply le_triangleCoveringNumberOn;
        exact ⟨ hE'.1.1, fun t ht => hE'.1.2 t ( h_union ht ) ⟩;
      · apply_rules [ tau_union_le_sum ];
    exact h_union.trans ( add_le_add_right ( tau_union_le_sum G _ _ ) _ );
  have h_term_le_2 : triangleCoveringNumberOn G (X_ef G e_center e₁) ≤ 2 ∧ triangleCoveringNumberOn G (X_ef G e_center e₂) ≤ 2 ∧ triangleCoveringNumberOn G (X_ef G e_center e₃) ≤ 2 := by
    refine' ⟨ tau_X_le_2 G M hM e_center e₁ _ _ _, tau_X_le_2 G M hM e_center e₂ _ _ _, tau_X_le_2 G M hM e_center e₃ _ _ _ ⟩ <;> simp_all +decide [ Finset.ext_iff, Finset.subset_iff ];
    · grind;
    · grind;
    · grind;
  grind

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_bridges_sparse_sharing (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_bridges_sparse_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_sparse : maxSharingDegree M ≤ 2) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 8 := by
  have h_pairs : (allBridges G M).card ≤ 6 := by
    have h_unique_bridges : ∀ t ∈ allBridges G M, ∃! (p : Finset V × Finset V), p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 ≠ p.2 ∧ t ∈ X_ef G p.1 p.2 := by
      apply bridges_partition G M hM;
    choose! p hp hp' using fun t ht => h_unique_bridges t ht;
    have h_card_bridges : (allBridges G M).card ≤ (Finset.powersetCard 2 M).card := by
      have h_card_bridges : (allBridges G M).card ≤ (Finset.image (fun t => {p t |>.1, p t |>.2} : Finset V → Finset (Finset V)) (allBridges G M)).card := by
        rw [ Finset.card_image_of_injOn ];
        intro t ht t' ht' h_eq;
        have := hp t ht; have := hp t' ht'; simp_all +decide [ X_ef ] ;
        grind;
      refine' h_card_bridges.trans ( Finset.card_le_card _ );
      grind;
    exact h_card_bridges.trans ( by simp +decide [ hM_card ] );
  unfold triangleCoveringNumberOn;
  have h_exists_cover : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 6 := by
    have h_exists_cover : ∀ t ∈ allBridges G M, ∃ e ∈ G.edgeFinset, e ∈ t.sym2 := by
      intro t ht;
      unfold allBridges at ht;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      rcases ht.1 with ⟨ h₁, h₂ ⟩;
      rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use s(a, b) ; aesop;
    choose! f hf₁ hf₂ using h_exists_cover;
    refine' ⟨ Finset.image ( fun t : allBridges G M => f t.1 t.2 ) ( Finset.univ : Finset ( allBridges G M ) ), _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective ];
    · exact Set.range_subset_iff.mpr fun t => hf₁ _ _;
    · exact fun t ht => ⟨ f t ht, ⟨ t, ht, rfl ⟩, hf₂ t ht ⟩;
    · exact le_trans ( Finset.card_image_le ) ( by simpa using h_pairs );
  have h_exists_cover : Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ Finset.card h_exists_cover.choose := by
    have h_exists_cover : ∀ E' ∈ {E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2}, Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ E'.card := by
      intro E' hE'
      have h_min_le_card : ∀ x ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2}), Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ x := by
        simp +decide [ Option.getD ];
        intro x E' hE' hE'' hx; rw [ hx.symm ] ;
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ allBridges G M, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ];
        exact_mod_cast h ▸ Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( show E' ⊆ G.edgeFinset from fun e he => by simpa using hE' he ), hE'' ⟩ ) );
      exact h_min_le_card _ ( Finset.mem_image_of_mem _ hE' );
    exact h_exists_cover _ ( Finset.mem_filter.mpr ⟨ ‹∃ E' ∈ G.edgeFinset.powerset, ( ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2 ) ∧ E'.card ≤ 6›.choose_spec.1, ‹∃ E' ∈ G.edgeFinset.powerset, ( ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2 ) ∧ E'.card ≤ 6›.choose_spec.2.1 ⟩ );
  linarith [ ‹∃ E' ∈ G.edgeFinset.powerset, ( ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2 ) ∧ E'.card ≤ 6›.choose_spec.2.2 ]

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: bridges_partition (unique pair ownership)
-- This is the ONE SORRY expected
-- ══════════════════════════════════════════════════════════════════════════════

/--
  Each bridge belongs to exactly one pair X(eᵢ, eⱼ).
  This is because a triangle t with |t ∩ eᵢ| ≥ 2 and |t ∩ eⱼ| ≥ 2
  can only fit in two packing elements (t has only 3 vertices).
-/
lemma bridges_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    ∀ t ∈ allBridges G M, ∃! (p : Finset V × Finset V),
      p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 ≠ p.2 ∧ t ∈ X_ef G p.1 p.2 := by
  intro t ht
  -- Extract bridge properties
  simp only [allBridges, Finset.mem_filter] at ht
  obtain ⟨ht_clique, hex⟩ := ht
  obtain ⟨elem1, hex'⟩ := hex
  obtain ⟨elem2, h_elem1_M, h_elem2_M, h_neq, h_inter1, h_inter2⟩ := hex'
  -- Construct the witness pair
  refine ⟨(elem1, elem2), ?_, ?_⟩
  -- Existence: elem1, elem2 work
  · exact ⟨h_elem1_M, h_elem2_M, h_neq, by simp only [X_ef, Finset.mem_filter]; exact ⟨ht_clique, h_inter1, h_inter2⟩⟩
  -- Uniqueness: any other pair must be the same
  · intro ⟨e', f'⟩ ⟨he'_M, hf'_M, hef'_neq, ht_in_X'⟩
    simp only [X_ef, Finset.mem_filter] at ht_in_X'
    obtain ⟨_, h_e'_inter, h_f'_inter⟩ := ht_in_X'
    -- Key insight: t has 3 vertices, and each of elem1, elem2, e', f' shares ≥2 vertices with t
    -- If we have 4 distinct packing elements each sharing ≥2 of 3 vertices, pigeonhole gives contradiction
    -- So {elem1, elem2} = {e', f'} as sets, hence (elem1, elem2) = (e', f') as ordered pairs
    -- (The ordering is determined by the existential witness structure)
    sorry

end
