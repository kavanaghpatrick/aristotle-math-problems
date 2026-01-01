/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e21aef61-c03d-4981-bd28-fc9f14837549

The following was proved by Aristotle:

- lemma triangles_containing_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (trianglesContaining G (T_pair G e f) v) ≤ 4

- lemma triangles_avoiding_share_base (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ trianglesAvoiding G (T_pair G e f) v) :
    (∃ ab : Finset V, ab ⊆ e ∧ ab.card = 2 ∧ v ∉ ab ∧ ab ⊆ t) ∨
    (∃ cd : Finset V, cd ⊆ f ∧ cd.card = 2 ∧ v ∉ cd ∧ cd ⊆ t)

- lemma triangles_avoiding_covered_by_bases (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding G (T_pair G e f) v) ≤ 2
-/

/-
slot62: tau_adjacent_pair_le_4 via Explicit Case Analysis + Full Scaffolding

ULTRATHINK ANALYSIS (Dec 31, 2025):
Combines:
- All 14 PROVEN lemmas from slot49a (UUID: 94272330)
- Explicit case split structure for the main theorem
- Cover overlap insight: 4 spokes from v suffice

MATHEMATICAL INSIGHT:
The gap is proving τ(T_pair) ≤ 4 when naive bound gives 6.

Key: Covers overlap through shared vertex v!
- e = {v,a,b}, f = {v,c,d}
- All triangles in T_pair share edge with e OR f
- But most share VERTEX v (only base triangles avoid v)
- 4 spokes {va, vb, vc, vd} cover:
  * All of S_e containing v (need spoke through common edge)
  * All of S_f containing v
  * All bridges X_ef (which contain v by bridges_contain_v)
  * Base triangles need separate treatment

CASE SPLIT (via Se_structure_lemma):
1. Both have common edge through v → spokes cover
2. One base edge, one spoke → 4 edges suffice
3. Both base edges → {a,b}, {c,d} + 2 spokes = 4 edges
4. External vertices → already covered by tau_S_le_2
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

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN INFRASTRUCTURE (from slot49a UUID: 94272330)
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangleCover (G : SimpleGraph V) (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

lemma isTriangleCover_union (G : SimpleGraph V) (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) :=
  ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_left _ he₁, he₂ ⟩ ; exact hB.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_right _ he₁, he₂ ⟩ ] ⟩

lemma triangleCoveringNumberOn_le_of_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  have h_min : triangleCoveringNumberOn G triangles ≤ Finset.min (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card) := by
    unfold triangleCoveringNumberOn;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 ) G.edgeFinset.powerset ) ) <;> aesop;
  contrapose! h_min;
  refine' lt_of_le_of_lt _ ( WithTop.coe_lt_coe.mpr h_min );
  simp +decide [ Finset.min ];
  exact ⟨ E', ⟨ fun e he => by have := h.1 he; aesop, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := h.2 t ht; aesop ⟩, le_rfl ⟩

lemma exists_min_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ∃ E', isTriangleCover G triangles E') :
    ∃ E', isTriangleCover G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G triangles E' ∧ ∀ E'' : Finset (Sym2 V), isTriangleCover G triangles E'' → E'.card ≤ E''.card := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ _, fun a ha => ha.1 ⟩;
  use E';
  unfold triangleCoveringNumberOn;
  rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 } ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from ?_ ];
  · rw [ show Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from rfl, Finset.min_eq_inf_withTop ];
    rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) ).inf WithTop.some = WithTop.some E'.card from ?_ ] ; aesop;
    refine' le_antisymm _ _ <;> simp_all +decide [ Finset.inf_le ];
    exact ⟨ E', ⟨ fun e he => by have := hE'.1.1 he; aesop, hE'.1 ⟩, le_rfl ⟩;
  · ext; simp [isTriangleCover]

lemma triangleCoveringNumberOn_eq_zero_of_not_coverable (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ ∃ E', isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles = 0 := by
  unfold triangleCoveringNumberOn;
  simp_all +decide [ Finset.min ];
  rw [ Finset.inf_eq_iInf ];
  rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
  case b => exact ⊤;
  · rfl;
  · simp_all +decide [ isTriangleCover ];
  · aesop

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · obtain ⟨E_A, hE_A⟩ := exists_min_isTriangleCover G A hA
      obtain ⟨E_B, hE_B⟩ := exists_min_isTriangleCover G B hB;
      have h_union : isTriangleCover G (A ∪ B) (E_A ∪ E_B) := by
        exact isTriangleCover_union G A B E_A E_B hE_A.1 hE_B.1;
      exact le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover _ _ _ h_union ) ( by rw [ ← hE_A.2, ← hE_B.2 ] ; exact Finset.card_union_le _ _ );
    · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
      · exact Nat.zero_le _;
      · exact fun ⟨ E', hE' ⟩ => hB ⟨ E', by exact ⟨ Finset.Subset.trans hE'.1 ( Finset.Subset.refl _ ), fun t ht => hE'.2 t ( Finset.mem_union_right _ ht ) ⟩ ⟩;
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
    · exact Nat.zero_le _;
    · exact fun ⟨ E', hE' ⟩ => hA ⟨ E', ⟨ hE'.1, fun t ht => hE'.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (bridges through shared vertex)
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  simp_all +decide [ Finset.ext_iff, X_ef ];
  by_contra hv_not_in_t
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx hx' => hv_not_in_t <| by have := hv x; aesop;
  have h_card : (t ∩ e) ∪ (t ∩ f) ⊆ t := by
    aesop_cat;
  have := Finset.card_le_card h_card; simp_all +decide [ Finset.card_union_add_card_inter ] ;
  linarith [ ht.1.card_eq ]

lemma X_ef_covering_number_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  simp_all +decide [ SimpleGraph.cliqueFinset ];
  set E' : Finset (Sym2 V) := Finset.image (fun u => Sym2.mk (v, u)) (e \ {v}) with hE';
  have h_cover : ∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2 := by
    intro t ht
    have h_triangle : v ∈ t := by
      unfold X_ef at ht;
      simp_all +decide [ Finset.ext_iff ];
      contrapose! ht;
      intro ht ht';
      have h_card : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        rw [ show t ∩ e ∪ t ∩ f = t ∩ ( e ∪ f ) by ext; aesop, show t ∩ e ∩ ( t ∩ f ) = ∅ by ext; aesop ] ; simp +decide;
      have h_card : (t ∩ (e ∪ f)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      linarith [ ht.2 ];
    obtain ⟨u, hu⟩ : ∃ u ∈ e \ {v}, u ∈ t := by
      have h_card : (t ∩ e).card ≥ 2 := by
        unfold X_ef at ht; aesop;
      contrapose! h_card;
      rw [ show t ∩ e = { v } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_inter.mpr ⟨ h_triangle, by replace hv := Finset.ext_iff.mp hv v; aesop ⟩, fun x hx => by_contradiction fun hx' => h_card x ( by aesop ) ( Finset.mem_inter.mp hx |>.1 ) ⟩ ] ; simp +decide;
    aesop;
  have h_covering : E' ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2) := by
    simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
    rintro _ u hu huv rfl; have := he.1 ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop ) ( show u ∈ e from hu ) ; aesop;
  have h_card_E' : E'.card ≤ 2 := by
    have := he.card_eq;
    grind;
  refine' le_trans ( _ : triangleCoveringNumberOn G ( X_ef G e f ) ≤ E'.card ) h_card_E';
  have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
    intros S hS; exact (by
    have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Option.getD (Finset.min S) 0 ≤ E'.card := by
      intro S hS; exact (by
      have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Finset.min S ≤ E'.card := by
        exact fun { S } hS => Finset.min_le hS;
      specialize h_min_le_card hS; cases h : Finset.min S <;> aesop;);
    exact h_min_le_card ( Finset.mem_image_of_mem _ hS ));
  exact h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_covering.1, h_covering.2 ⟩ )

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  apply X_ef_covering_number_le_2 G e f v hv;
  exact hM.1.1 he

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (and Se_structure_lemma)
-- ══════════════════════════════════════════════════════════════════════════════

lemma pairwise_intersecting_Se_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    Set.Pairwise ((S_e G M e).filter (· ≠ e) : Set (Finset V)) (fun t1 t2 => 2 ≤ (t1 ∩ t2).card) := by
  by_contra h_contra
  obtain ⟨t1, t2, ht1, ht2, h_disjoint⟩ : ∃ t1 t2 : Finset V, t1 ≠ t2 ∧ t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ (t1 ∩ t2).card ≤ 1 := by
    rw [ Set.Pairwise ] at h_contra;
    grind;
  have h_disjoint_M : ∀ f ∈ M \ {e}, (t1 ∩ f).card ≤ 1 ∧ (t2 ∩ f).card ≤ 1 := by
    unfold S_e at *; aesop;
  have h_packing : isTrianglePacking G ((M \ {e}) ∪ {t1, t2}) := by
    constructor;
    · intro x hx;
      simp +zetaDelta at *;
      rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> simp_all +decide [ S_e ];
      · unfold trianglesSharingEdge at ht2; aesop;
      · unfold trianglesSharingEdge at h_disjoint; aesop;
      · have := hM.1.1 hx; aesop;
    · simp_all +decide [ Set.Pairwise ];
      refine' ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint.2.2.2, fun a ha ha' => ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.1, fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.2, fun b hb hb' hab => _ ⟩ ⟩;
      have := hM.1;
      have := this.2 ha hb hab; aesop;
  have h_card : ((M \ {e}) ∪ {t1, t2}).card > M.card := by
    have h_card : ((M \ {e}) ∪ {t1, t2}).card = (M \ {e}).card + 2 := by
      have h_card : Disjoint (M \ {e}) {t1, t2} := by
        simp_all +decide [ Finset.disjoint_left ];
        intro f hf hfe; have := h_packing.1; simp_all +decide [ Finset.subset_iff ] ;
        constructor <;> intro h <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · grind;
        · have := h_disjoint_M t2 hf; simp_all +decide ;
      rw [ Finset.card_union_of_disjoint h_card, Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
    simp_all +decide [ Finset.card_sdiff ];
    omega;
  have h_contradiction : ((M \ {e}) ∪ {t1, t2}).card ≤ trianglePackingNumber G := by
    have h_contradiction : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro S hS;
      have h_contradiction : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by exact fun x hx => by have := hS.1 hx; aesop ), hS ⟩, rfl ⟩;
      have := Finset.le_max h_contradiction;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_contradiction _ h_packing;
  exact h_card.not_le ( h_contradiction.trans ( hM.2.ge ) )

lemma common_ext_vertex_of_diff_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V)
    (ht1 : t1 ∈ (S_e G M e).filter (· ≠ e))
    (ht2 : t2 ∈ (S_e G M e).filter (· ≠ e))
    (h_diff : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} ∧ t2 = (t2 ∩ e) ∪ {x} := by
  have h_inter : 2 ≤ (t1 ∩ t2).card := by
    have := pairwise_intersecting_Se_aux G M hM e he;
    exact this ht1 ht2 ( by aesop );
  have ht1_card : t1.card = 3 := by
    simp +zetaDelta at *;
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht1.1.1.1.2
  have ht2_card : t2.card = 3 := by
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht2.1.1.1.2;
  have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
    have ht1_inter_e_card_ge2 : 2 ≤ (t1 ∩ e).card := by
      simp +zetaDelta at *;
      exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht1.1 |>.1 ) |>.2;
    have ht1_inter_e_card_le3 : (t1 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht1_card.le;
    interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this; simp_all +decide ;
    have := hM.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
    have ht2_inter_e_card : 2 ≤ (t2 ∩ e).card := by
      unfold S_e at ht2;
      unfold trianglesSharingEdge at ht2; aesop;
    have ht2_inter_e_card : (t2 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht2_card.le;
    interval_cases _ : Finset.card ( t2 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t2 ∩ e ⊆ t2 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this ; simp_all +decide ;
    have := hM.1.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  obtain ⟨x, hx⟩ : ∃ x, x ∈ t1 ∧ x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} := by
    have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
    obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp this; use x; simp_all +decide [ Finset.ext_iff ] ;
    exact ⟨ by specialize hx x; tauto, by specialize hx x; tauto, fun a => ⟨ fun ha => by specialize hx a; tauto, fun ha => by specialize hx a; tauto ⟩ ⟩
  obtain ⟨y, hy⟩ : ∃ y, y ∈ t2 ∧ y ∉ e ∧ t2 = (t2 ∩ e) ∪ {y} := by
    have h_diff_t2 : (t2 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t2 e; simp +decide [ ht2_card, ht2_inter_e_card ] at this ⊢; linarith;
    obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_diff_t2;
    exact ⟨ y, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.left, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.right, by ext z; by_cases hz : z ∈ e <;> simp +decide [ hz, hy.symm ] ⟩;
  have hxy : x = y := by
    contrapose! h_inter;
    have h_inter_eq : t1 ∩ t2 = (t1 ∩ e) ∩ (t2 ∩ e) := by
      grind;
    rw [ h_inter_eq ];
    refine' lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ht1_inter_e_card.le ) _;
    intro H;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t1 ∩ e ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t2 ∩ e ) ; simp +decide [ H, ht1_inter_e_card, ht2_inter_e_card ] at *;
    grind +ring;
  grind

lemma Se_structure_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ uv, uv ⊆ e ∧ uv.card = 2 ∧ ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) ∨
    (∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) := by
  by_cases h : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
  · obtain ⟨ t1, t2, ht1, ht2, h1, h2, h3 ⟩ := h;
    obtain ⟨ x, hx ⟩ := common_ext_vertex_of_diff_edges G M hM e he t1 t2 ( by aesop ) ( by aesop ) h3;
    refine' Or.inr ⟨ x, hx.1, fun t ht ht' => _ ⟩;
    by_cases h4 : t ∩ e = t1 ∩ e;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t2 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht2, h2 ⟩ ) ( by
        exact h4.symm ▸ h3 );
      grind;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t1 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht1, h1 ⟩ ) h4;
      grind;
  · by_cases h_empty : S_e G M e \ {e} = ∅;
    · simp_all +decide [ Finset.ext_iff ];
      contrapose! h_empty;
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      have := this.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      exact False.elim ( h_empty.1 ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.left ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.right ) );
    · obtain ⟨t, ht⟩ : ∃ t ∈ S_e G M e \ {e}, ∀ t' ∈ S_e G M e \ {e}, t ∩ e = t' ∩ e := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, fun t' ht' => Classical.not_not.1 fun h' => h ⟨ t, t', by aesop ⟩ ⟩;
      have := Finset.mem_filter.mp ( Finset.mem_sdiff.mp ht.1 |>.1 );
      have := Finset.mem_filter.mp this.1;
      obtain ⟨uv, huv⟩ : ∃ uv ⊆ t ∩ e, uv.card = 2 := by
        exact Finset.exists_subset_card_eq this.2;
      grind

lemma tau_S_le_2_case1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (uv : Finset V) (huv : uv ⊆ e) (huv_card : uv.card = 2)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  unfold triangleCoveringNumberOn;
  obtain ⟨u, v, hu, hv, huv_eq⟩ : ∃ u v, uv = {u, v} ∧ u ≠ v ∧ u ∈ e ∧ v ∈ e := by
    rw [ Finset.card_eq_two ] at huv_card; obtain ⟨ u, v, huv ⟩ := huv_card; use u, v; aesop;
  have huv_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
    have := hM.1.1 he; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
    exact this.1 ( by aesop ) ( by aesop ) hv;
  have h_triangle_covering : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ 2 := by
    refine' ⟨ { Sym2.mk ( u, v ) }, _, _ ⟩ <;> simp_all +decide;
    intro t ht; specialize h_struct t ht; by_cases h : t = e <;> simp_all +decide [ Finset.subset_iff ] ;
  obtain ⟨ E', hE₁, hE₂ ⟩ := h_triangle_covering;
  have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ );
  exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE₂

lemma tau_S_le_2_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (x : V) (hx : x ∉ e)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ G.Adj u v := by
    have := hM.1;
    have := this.1 he; simp +decide [ isTrianglePacking ] at this;
    rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v ; simp_all +decide [ SimpleGraph.isNClique_iff ];
  obtain ⟨w, hw⟩ : ∃ w : V, w ∈ e ∧ w ≠ u ∧ w ≠ v := by
    have h_card : e.card = 3 := by
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.card_eq;
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase e u ) from by rw [ Finset.card_erase_of_mem huv.1, h_card ] ; decide ) v );
  by_cases huv_cover : ∀ t ∈ S_e G M e, t ≠ e → (u ∈ t ∧ v ∈ t) ∨ (w ∈ t ∧ x ∈ t);
  · set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)};
    have hE'_cover : ∀ t ∈ S_e G M e, t ≠ e → ∃ e' ∈ E', e' ∈ t.sym2 := by
      intro t ht ht'; specialize huv_cover t ht ht'; rcases huv_cover with ( ⟨ hu, hv ⟩ | ⟨ hw, hx ⟩ ) <;> [ exact ⟨ _, Finset.mem_insert_self _ _, by simp +decide [ hu, hv ] ⟩ ; exact ⟨ _, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ), by simp +decide [ hw, hx ] ⟩ ] ;
    have h_triangleCoveringNumberOn_le_2 : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
      refine' ⟨ E' ∩ G.edgeFinset, _, _, _ ⟩;
      · exact Finset.inter_subset_right;
      · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_insert_le _ _ );
      · intro t ht;
        by_cases h : t = e <;> simp +decide [ h ] at hE'_cover ⊢;
        · exact ⟨ Sym2.mk ( u, v ), ⟨ Finset.mem_insert_self _ _, by simpa using huv.2.2.2 ⟩, by simp +decide [ huv.1, huv.2.1 ] ⟩;
        · obtain ⟨ e', he', he'' ⟩ := hE'_cover t ht h;
          simp +zetaDelta at *;
          rcases he' with ( rfl | rfl ) <;> [ exact ⟨ _, ⟨ Or.inl rfl, by simpa using huv.2.2.2 ⟩, he'' ⟩ ; exact ⟨ _, ⟨ Or.inr rfl, by
            have := Finset.mem_filter.mp ht |>.1; simp +decide [ SimpleGraph.mem_edgeSet ] at this ⊢;
            unfold trianglesSharingEdge at this; simp +decide [ SimpleGraph.mem_edgeSet ] at this;
            have := this.1.1; simp +decide [ SimpleGraph.isNClique_iff ] at this;
            exact this ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inl rfl ) ) ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inr rfl ) ) ( by rintro rfl; simp +decide [ hx ] at * ) ⟩, he'' ⟩ ];
    obtain ⟨ E', hE'_sub, hE'_card, hE'_cover ⟩ := h_triangleCoveringNumberOn_le_2;
    have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
      intro S hS; have := Finset.min_le ( Finset.mem_image_of_mem Finset.card hS ) ; simp +decide at this ⊢;
      cases h : Finset.min ( Finset.image Finset.card S ) <;> simp +decide [ h ] at this ⊢ ; exact this;
    exact le_trans ( h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩ ) ) hE'_card;
  · contrapose! huv_cover;
    intro t ht hte
    have ht_edges : t ∩ e = {u, v} ∨ t ∩ e = {v, w} ∨ t ∩ e = {u, w} := by
      have ht_edges : (t ∩ e).card = 2 := by
        have := h_struct t ht hte;
        have ht_card : t.card = 3 := by
          unfold S_e at ht; norm_num at ht;
          unfold trianglesSharingEdge at ht; norm_num at ht;
          exact ht.1.1.card_eq;
        rw [ this, Finset.card_union ] at ht_card ; simp +decide [ hx ] at ht_card ⊢ ; linarith;
      have ht_edges_subset : t ∩ e ⊆ {u, v, w} := by
        have := hM.1;
        have := this.1 he; simp +decide [ SimpleGraph.cliqueFinset ] at this;
        have := this.2; simp +decide [ Finset.card_eq_three ] at this;
        grind;
      have := Finset.card_eq_two.mp ht_edges;
      rcases this with ⟨ x, y, hxy, h ⟩ ; simp +decide [ h, Finset.Subset.antisymm_iff, Finset.subset_iff ] at ht_edges_subset ⊢;
      grind;
    rcases ht_edges with ( h | h | h ) <;> specialize h_struct t ht hte <;> simp +decide [ h ] at h_struct ⊢;
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ]

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain h | h := Se_structure_lemma G M hM e he
  · exact tau_S_le_2_case1 G M hM e he _ h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2
  · exact tau_S_le_2_case2 G M hM e he h.choose h.choose_spec.left h.choose_spec.right

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: Triangles containing vs avoiding shared vertex v
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

lemma T_pair_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) :
    T_pair G e f = trianglesContaining G (T_pair G e f) v ∪ trianglesAvoiding G (T_pair G e f) v := by
  ext t
  simp only [T_pair, trianglesContaining, trianglesAvoiding, Finset.mem_union, Finset.mem_filter]
  tauto

/-- Triangles containing v can be covered by 4 spokes from v -/
lemma triangles_containing_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (trianglesContaining G (T_pair G e f) v) ≤ 4 := by
  -- The 4 spokes from v cover all triangles containing v
  -- e = {v, a, b}, f = {v, c, d}
  -- Spokes: {v,a}, {v,b}, {v,c}, {v,d}
  -- Any triangle containing v has at least one edge {v,x} for x ∈ {a,b,c,d}
  -- Let $x$ and $y$ be the vertices of $e$ distinct from $v$, and $w$ and $z$ be the vertices of $f$ distinct from $v$.
  obtain ⟨x, y, hx, hy⟩ : ∃ x y : V, x ≠ y ∧ e = {v, x, y} := by
    simp_all +decide [ SimpleGraph.cliqueFinset ];
    have := Finset.card_eq_three.mp he.2;
    obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := this;
    rw [ Finset.eq_singleton_iff_unique_mem ] at hv;
    simp +zetaDelta at *;
    rcases hv.1.1 with ( rfl | rfl | rfl ) <;> simp_all +decide;
    · exact ⟨ y, z, hyz, rfl ⟩;
    · exact ⟨ x, z, hxz, by ext; aesop ⟩;
    · exact ⟨ x, y, hxy, by ext; aesop ⟩
  obtain ⟨w, z, hw, hz⟩ : ∃ w z : V, w ≠ z ∧ f = {v, w, z} := by
    have h_card_f : f.card = 3 := by
      exact Finset.mem_filter.mp ( Finset.mem_coe.mpr hf ) |>.2.2;
    rw [ Finset.card_eq_three ] at h_card_f;
    obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := h_card_f;
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    rcases hv.1 with ( rfl | rfl | rfl ) <;> simp_all +decide [ Finset.ext_iff ];
    · exact ⟨ y, z, hyz, fun a => by tauto ⟩;
    · exact ⟨ x, z, hxz, by tauto ⟩;
    · exact ⟨ x, y, hxy, by tauto ⟩;
  -- The set of edges $\{vx, vy, vw, vz\}$ covers all triangles containing $v$.
  have h_cover : isTriangleCover G (trianglesContaining G (T_pair G e f) v) {Sym2.mk (v, x), Sym2.mk (v, y), Sym2.mk (v, w), Sym2.mk (v, z)} := by
    refine' ⟨ _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff, SimpleGraph.mem_edgeFinset ];
      simp_all +decide [ SimpleGraph.isNClique_iff, Finset.ext_iff ];
      grind;
    · intro t ht; simp_all +decide [ trianglesContaining, T_pair ] ;
      rcases ht.1 with ( ht | ht ) <;> simp_all +decide [ trianglesSharingEdge ];
      · contrapose! ht; simp_all +decide [ Finset.ext_iff ] ;
      · contrapose! ht; simp_all +decide [ Finset.ext_iff ] ;
  refine' le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover _ _ _ h_cover ) _;
  exact Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ ) _ ) _

/-- Triangles avoiding v in T_pair share edge with base of e or f -/
lemma triangles_avoiding_share_base (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ trianglesAvoiding G (T_pair G e f) v) :
    (∃ ab : Finset V, ab ⊆ e ∧ ab.card = 2 ∧ v ∉ ab ∧ ab ⊆ t) ∨
    (∃ cd : Finset V, cd ⊆ f ∧ cd.card = 2 ∧ v ∉ cd ∧ cd ⊆ t) := by
  -- If t avoids v but shares edge with e, it must share the base edge {a,b}
  -- Similarly for f
  unfold trianglesAvoiding T_pair at ht;
  unfold trianglesSharingEdge at ht;
  simp_all +decide [ Finset.filter_union, Finset.filter_filter ];
  rcases ht with ( ⟨ ht₁, ht₂, ht₃ ⟩ | ⟨ ht₁, ht₂, ht₃ ⟩ );
  · obtain ⟨ ab, hab ⟩ := Finset.exists_subset_card_eq ht₂;
    exact Or.inl ⟨ ab, fun x hx => Finset.mem_of_mem_inter_right ( hab.1 hx ), hab.2, fun hx => ht₃ ( hab.1 hx |> Finset.mem_of_mem_inter_left ), fun x hx => Finset.mem_of_mem_inter_left ( hab.1 hx ) ⟩;
  · obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ht₂;
    exact Or.inr ⟨ { x, y }, by aesop_cat, by aesop_cat, by aesop_cat, by aesop_cat ⟩

/- Triangles avoiding v can be covered by 2 base edges -/
noncomputable section AristotleLemmas

/-
If every triangle in T contains one of two given edges (cliques of size 2), then the covering number of T is at most 2.
-/
lemma triangleCoveringNumberOn_le_2_of_subset_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (e1 e2 : Finset V)
    (h1 : e1.card = 2) (h2 : e2.card = 2)
    (he1 : G.IsClique e1) (he2 : G.IsClique e2)
    (h : ∀ t ∈ T, e1 ⊆ t ∨ e2 ⊆ t) :
    triangleCoveringNumberOn G T ≤ 2 := by
      obtain ⟨x, y, hx, hy⟩ : ∃ x y : V, e1 = {x, y} := by
        rw [ Finset.card_eq_two ] at h1; tauto;
      obtain ⟨u, v, hu, hv⟩ : ∃ u v : V, e2 = {u, v} := by
        rw [ Finset.card_eq_two ] at h2; tauto;
      refine' le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover G T _ _ ) _;
      exact { Sym2.mk ( x, y ), Sym2.mk ( u, v ) };
      · refine' ⟨ _, _ ⟩;
        · intro; aesop;
        · intro t ht; specialize h t ht; aesop;
      · exact Finset.card_insert_le _ _

end AristotleLemmas

lemma triangles_avoiding_covered_by_bases (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding G (T_pair G e f) v) ≤ 2 := by
  -- Base edge of e covers all avoiding that share with e
  -- Base edge of f covers all avoiding that share with f
  have h_base_edges : ∃ e_base f_base : Finset V, e_base ⊆ e ∧ e_base.card = 2 ∧ v∉ e_base ∧ f_base ⊆ f ∧ f_base.card = 2 ∧ v∉ f_base ∧ ∀ t ∈ trianglesAvoiding G (T_pair G e f) v, e_base ⊆ t ∨ f_base ⊆ t := by
    have h_base_edges : ∀ t ∈ trianglesAvoiding G (T_pair G e f) v, (∃ ab : Finset V, ab ⊆ e ∧ ab.card = 2 ∧ v∉ ab ∧ ab ⊆ t) ∨ (∃ cd : Finset V, cd ⊆ f ∧ cd.card = 2 ∧ v∉ cd ∧ cd ⊆ t) := by
      exact?;
    have h_base_edges : e.card = 3 ∧ f.card = 3 := by
      have := hM.1;
      have := this.1;
      simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ];
      exact ⟨ this he |>.2, this hf |>.2 ⟩;
    have h_base_edges : ∃ e_base : Finset V, e_base ⊆ e ∧ e_base.card = 2 ∧ v∉ e_base ∧ ∀ ab : Finset V, ab ⊆ e → ab.card = 2 → v∉ ab → ab = e_base := by
      have h_base_edges : Finset.card (e.erase v) = 2 := by
        rw [ Finset.card_erase_of_mem ( show v ∈ e from Finset.mem_of_mem_inter_left ( hv.symm ▸ Finset.mem_singleton_self _ ) ), h_base_edges.1 ];
      use e.erase v;
      simp_all +decide [ Finset.subset_iff ];
      intro ab hab hcard hv; have := Finset.eq_of_subset_of_card_le ( show ab ⊆ e.erase v from fun x hx => Finset.mem_erase_of_ne_of_mem ( by aesop ) ( hab hx ) ) ; aesop;
    have h_base_edges_f : ∃ f_base : Finset V, f_base ⊆ f ∧ f_base.card = 2 ∧ v∉ f_base ∧ ∀ cd : Finset V, cd ⊆ f → cd.card = 2 → v∉ cd → cd = f_base := by
      have h_base_edges_f : f \ {v} ∈ Finset.powersetCard 2 f := by
        grind;
      use f \ {v};
      simp_all +decide [ Finset.mem_powersetCard ];
      intro cd hcd hcd' hvcd; rw [ Finset.eq_of_subset_of_card_le ( show cd ⊆ f \ { v } from fun x hx => Finset.mem_sdiff.mpr ⟨ hcd hx, by aesop ⟩ ) ( by aesop ) ] ;
    obtain ⟨ e_base, he_base₁, he_base₂, he_base₃, he_base₄ ⟩ := h_base_edges
    obtain ⟨ f_base, hf_base₁, hf_base₂, hf_base₃, hf_base₄ ⟩ := h_base_edges_f
    use e_base, f_base;
    grind;
  obtain ⟨ e_base, f_base, he_base, he_base_card, hv_base, hf_base, hf_base_card, hv_base', h ⟩ := h_base_edges;
  refine' triangleCoveringNumberOn_le_2_of_subset_union _ _ _ _ _ _ _ _ h;
  · exact he_base_card;
  · exact hf_base_card;
  · have := hM.1;
    have := this.1 he; simp_all +decide [ SimpleGraph.isClique_iff, Finset.subset_iff ] ;
    exact fun x hx y hy hxy => this.1 ( he_base hx ) ( he_base hy ) hxy;
  · have := hM.1;
    have := this.1 hf; simp_all +decide [ SimpleGraph.isClique_iff ] ;
    exact fun x hx y hy hxy => this.1 ( hf_base hx ) ( hf_base hy ) hxy

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Use split + overlap argument
-- ══════════════════════════════════════════════════════════════════════════════

/--
KEY INSIGHT: The covers OVERLAP at the shared vertex v!

Split T_pair into:
1. Triangles containing v: covered by ≤4 spokes
2. Triangles avoiding v: covered by ≤2 base edges

But wait - this gives 6 not 4!

The key is that when we use Se_structure_lemma, the common edge
or common external vertex structure allows for BETTER bounds.

Case analysis:
- If S_e all share edge through v (spoke): 1 spoke covers all of S_e
- If S_e all share base edge {a,b}: 1 base edge covers all of S_e
- If S_e has external vertex: tau_S_le_2 already proven

When both e and f have spoke structure, we need only:
- 1 spoke for S_e
- 1 spoke for S_f
- 2 spokes for bridges (tau_X_le_2)
= 4 edges total (but these overlap!)

When one has base, one has spoke:
- 1 base for S_e's avoiding triangles
- 1 spoke for S_e's containing triangles (same as S_f's coverage)
= Still need to work this out...
-/
theorem tau_adjacent_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- Strategy: Use Se_structure_lemma on both e and f
  -- Case split on which structure each has
  obtain ⟨uv_e, huv_e_sub, huv_e_card, huv_e_struct⟩ | ⟨x_e, hx_e_not, hx_e_struct⟩ :=
    Se_structure_lemma G M hM e he
  · -- Case: e has common edge uv_e
    obtain ⟨uv_f, huv_f_sub, huv_f_card, huv_f_struct⟩ | ⟨x_f, hx_f_not, hx_f_struct⟩ :=
      Se_structure_lemma G M hM f hf
    · -- Subcase 1.1: Both have common edges
      -- Check if uv_e and uv_f both go through v
      -- If so, we can cover with overlapping spokes
      sorry
    · -- Subcase 1.2: e has common edge, f has external vertex
      -- Combine the structures
      sorry
  · -- Case: e has external vertex x_e
    obtain ⟨uv_f, huv_f_sub, huv_f_card, huv_f_struct⟩ | ⟨x_f, hx_f_not, hx_f_struct⟩ :=
      Se_structure_lemma G M hM f hf
    · -- Subcase 2.1: e has external, f has common edge
      sorry
    · -- Subcase 2.2: Both have external vertices
      -- Key insight: might be the SAME external vertex!
      -- If x_e = x_f, covers overlap significantly
      sorry

end