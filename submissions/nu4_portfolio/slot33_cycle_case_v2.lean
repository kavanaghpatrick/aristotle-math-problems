/-
Tuza ν=4 Portfolio - Slot 33 v2: Cycle Configuration (C4)

TARGET: Prove τ ≤ 8 when sharing graph is a 4-cycle e1 — e2 — e3 — e4 — e1

CONFIGURATION:
- e1 ∩ e2 = {v12}
- e2 ∩ e3 = {v23}
- e3 ∩ e4 = {v34}
- e4 ∩ e1 = {v41}
- All four shared vertices are DISTINCT

KEY INSIGHT: Opposite pairs are vertex-disjoint (e1,e3) and (e2,e4)

FULL SCAFFOLDING INCLUDED (from proven Aristotle outputs)
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

def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e ∈ M, ∃ f ∈ M, e ≠ f ∧ (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: tau_union_le_sum (from slot16, UUID b4f73fa3-9cbc-4877-9819-f5e077da1c54)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A cover for A ∪ B is also a cover for A -/
lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

/-- A cover for A ∪ B is also a cover for B -/
lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

/-- Union of covers: if XA covers A and XB covers B, then XA ∪ XB covers A ∪ B -/
lemma union_covers_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (XA XB : Finset (Sym2 V))
    (hA : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2)
    (hB : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2) :
    ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htA | htB
  · obtain ⟨e, heXA, het⟩ := hA t htA
    exact ⟨e, Finset.mem_union_left XB heXA, het⟩
  · obtain ⟨e, heXB, het⟩ := hB t htB
    exact ⟨e, Finset.mem_union_right XA heXB, het⟩

/-- The key union bound lemma: τ(A ∪ B) ≤ τ(A) + τ(B) -/
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  let coversAB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2)
  let coversA := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)
  let coversB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2)
  let sizesAB := coversAB.image Finset.card
  let sizesA := coversA.image Finset.card
  let sizesB := coversB.image Finset.card

  by_cases hAB : sizesAB.Nonempty
  case pos =>
    have coversAB_sub_coversA : coversAB ⊆ coversA := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_left G A B E' hE'.2⟩
    have coversAB_sub_coversB : coversAB ⊆ coversB := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_right G A B E' hE'.2⟩
    have hA : sizesA.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversA)
    have hB : sizesB.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversB)

    have h_tauAB : triangleCoveringNumberOn G (A ∪ B) = sizesAB.min' hAB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauA : triangleCoveringNumberOn G A = sizesA.min' hA := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauB : triangleCoveringNumberOn G B = sizesB.min' hB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp

    have minA_mem : sizesA.min' hA ∈ sizesA := Finset.min'_mem sizesA hA
    have minB_mem : sizesB.min' hB ∈ sizesB := Finset.min'_mem sizesB hB

    obtain ⟨XA, hXA_mem, hXA_card⟩ := Finset.mem_image.mp minA_mem
    obtain ⟨XB, hXB_mem, hXB_card⟩ := Finset.mem_image.mp minB_mem

    have hXA_sub : XA ⊆ G.edgeFinset := (Finset.mem_filter.mp hXA_mem).1 |> Finset.mem_powerset.mp
    have hXA_covers : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2 := (Finset.mem_filter.mp hXA_mem).2
    have hXB_sub : XB ⊆ G.edgeFinset := (Finset.mem_filter.mp hXB_mem).1 |> Finset.mem_powerset.mp
    have hXB_covers : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2 := (Finset.mem_filter.mp hXB_mem).2

    have hUnion_covers : ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 :=
      union_covers_union G A B XA XB hXA_covers hXB_covers
    have hUnion_sub : XA ∪ XB ⊆ G.edgeFinset := Finset.union_subset hXA_sub hXB_sub
    have hUnion_mem : XA ∪ XB ∈ coversAB := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hUnion_sub, hUnion_covers⟩

    have card_union_mem : (XA ∪ XB).card ∈ sizesAB :=
      Finset.mem_image_of_mem Finset.card hUnion_mem
    have min_le_card : sizesAB.min' hAB ≤ (XA ∪ XB).card :=
      Finset.min'_le sizesAB (XA ∪ XB).card card_union_mem
    have card_union_le : (XA ∪ XB).card ≤ XA.card + XB.card := Finset.card_union_le XA XB

    calc triangleCoveringNumberOn G (A ∪ B)
        = sizesAB.min' hAB := h_tauAB
      _ ≤ (XA ∪ XB).card := min_le_card
      _ ≤ XA.card + XB.card := card_union_le
      _ = sizesA.min' hA + sizesB.min' hB := by rw [hXA_card, hXB_card]
      _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [← h_tauA, ← h_tauB]

  case neg =>
    have h_empty : sizesAB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAB
    have h_tau_zero : triangleCoveringNumberOn G (A ∪ B) = 0 := by
      simp only [triangleCoveringNumberOn]
      rw [h_empty]
      simp
    rw [h_tau_zero]
    exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: Te_eq_Se_union_bridges (from slot6)
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
-- PROVEN SCAFFOLDING: Se_pairwise_intersect (from slot6)
-- ══════════════════════════════════════════════════════════════════════════════

lemma Se_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (edge_e : Finset V) (he : edge_e ∈ M) :
    ∀ t1 ∈ S_e G M edge_e, ∀ t2 ∈ S_e G M edge_e, (t1 ∩ t2).card ≥ 2 := by
  intros t1 ht1 t2 ht2
  by_contra h
  push_neg at h
  have h_disj : (t1 ∩ t2).card ≤ 1 := Nat.le_of_lt_succ h

  have h_t1_in_T : t1 ∈ trianglesSharingEdge G edge_e := (Finset.mem_filter.mp ht1).1
  have h_t1_inter : (t1 ∩ edge_e).card ≥ 2 := (Finset.mem_filter.mp h_t1_in_T).2
  have h_t2_in_T : t2 ∈ trianglesSharingEdge G edge_e := (Finset.mem_filter.mp ht2).1
  have h_t2_inter : (t2 ∩ edge_e).card ≥ 2 := (Finset.mem_filter.mp h_t2_in_T).2

  have h_t1_ne_e : t1 ≠ edge_e := by
    intro heq
    rw [heq] at h_disj
    rw [Finset.inter_comm] at h_disj
    linarith
  have h_t2_ne_e : t2 ≠ edge_e := by
    intro heq
    rw [heq] at h_disj
    linarith

  let M' := (M.erase edge_e) ∪ {t1, t2}
  have h_packing : isTrianglePacking G M' := by
    have h_M_erase : isTrianglePacking G (M.erase edge_e) := by
      have := hM.1;
      exact ⟨ Finset.Subset.trans ( Finset.erase_subset _ _ ) this.1, fun x hx y hy hxy => this.2 ( Finset.mem_of_mem_erase hx ) ( Finset.mem_of_mem_erase hy ) hxy ⟩;
    have h_t1_t2 : ∀ t ∈ ({t1, t2} : Finset (Finset V)), ∀ f ∈ M.erase edge_e, (t ∩ f).card ≤ 1 := by
      unfold S_e at *; aesop;
    have h_t1_t2_subset : ({t1, t2} : Finset (Finset V)) ⊆ G.cliqueFinset 3 := by
      simp_all +decide [ Finset.subset_iff ];
      unfold trianglesSharingEdge at *; aesop;
    unfold isTrianglePacking at *;
    simp_all +decide [ Set.Pairwise ];
    simp +zetaDelta at *;
    simp_all +decide [ Finset.subset_iff, Finset.inter_comm ]
  have h_card : M'.card > M.card := by
    have h_card_add : (M.erase edge_e ∪ {t1, t2}).card = (M.erase edge_e).card + 2 := by
      have h_card_add : t1 ∉ M.erase edge_e ∧ t2 ∉ M.erase edge_e ∧ t1 ≠ t2 := by
        refine' ⟨ _, _, _ ⟩;
        · intro h;
          have := hM.1.2;
          exact h_t1_inter.not_lt ( lt_of_le_of_lt ( this ( Finset.mem_coe.2 ( Finset.mem_of_mem_erase h ) ) ( Finset.mem_coe.2 he ) ( by aesop ) ) ( by norm_num ) );
        · intro h; have := hM.1; simp_all +decide [ Finset.subset_iff ] ;
          have := this.2; simp_all +decide [ Set.Pairwise ] ;
          exact absurd ( this h he ( by aesop ) ) ( by linarith );
        · intro h_eq; simp_all +decide ;
          exact h_t2_inter.not_lt ( lt_of_le_of_lt ( Finset.card_le_card ( Finset.inter_subset_left ) ) h );
      rw [ Finset.card_union ] ; aesop;
    grind
  have h_le : M'.card ≤ trianglePackingNumber G := by
    have h_M'_subset : M' ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      unfold isTrianglePacking at *; aesop;
    unfold trianglePackingNumber;
    have h_M'_card_le_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
      intro x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_M'_card_le_max _ ( Finset.mem_image_of_mem _ h_M'_subset )
  rw [← hM.2] at h_le
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: tau_S_le_2 (from slot6, full proof)
-- ══════════════════════════════════════════════════════════════════════════════

lemma Se_common_vertex_implies_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_common : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      unfold triangleCoveringNumberOn;
      obtain ⟨v, hv_e, hv⟩ : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t := h_common;
      have h_cover : ∃ E' ⊆ G.edgeFinset, (∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2) ∧ E'.card ≤ 2 := by
        obtain ⟨u, w, hu, hw, he_eq⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ e = {v, u, w} := by
          have h_card_e : e.card = 3 := by
            have := hM.1.1;
            have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            exact this.2;
          have := Finset.card_eq_three.mp h_card_e;
          obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := this; use if x = v then y else if y = v then z else x, if x = v then z else if y = v then x else y; aesop;
        refine' ⟨ { s(v, u), s(v, w) }, _, _, _ ⟩ <;> simp_all +decide [ Set.Pairwise ];
        · have := hM.1.1 he; simp_all +decide [ SimpleGraph.mem_edgeSet, Sym2.eq ] ;
          simp_all +decide [ Set.insert_subset_iff, SimpleGraph.isNClique_iff ];
          grind;
        · intro t ht; specialize hv t ht; simp_all +decide [ Finset.subset_iff, S_e ] ;
          have := Finset.mem_filter.mp ht.1; simp_all +decide [ trianglesSharingEdge ] ;
          contrapose! ht; simp_all +decide [ Finset.card_insert_of_notMem, SimpleGraph.isNClique_iff ] ;;
      simp +zetaDelta at *;
      obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_cover;
      refine' le_trans _ hE₃;
      have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa [ ← Finset.coe_subset ] using hE₁ ), hE₂ ⟩, rfl ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

lemma Se_structure_step1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (u v w : V) (he_eq : e = {u, v, w}) (h_distinct : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (tu : Finset V) (htu : tu ∈ S_e G M e) (hu_tu : u ∉ tu)
    (tv : Finset V) (htv : tv ∈ S_e G M e) (hv_tv : v ∉ tv) :
    ∃ x, x ∉ ({u, v, w} : Finset V) ∧ tu = {v, w, x} ∧ tv = {u, w, x} := by
      have h_tu : ∃ x, tu = {v, w, x} := by
        have h_tu_card : tu.card = 3 := by
          have h_tu_card : tu ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp htu |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_tu_card |>.2.2;
        have h_tu_subset : v ∈ tu ∧ w ∈ tu := by
          have h_tu_subset : (tu ∩ e).card ≥ 2 := by
            unfold S_e at htu;
            unfold trianglesSharingEdge at htu; aesop;
          simp_all +decide [ Finset.inter_comm ];
          contrapose! h_tu_subset;
          exact lt_of_le_of_lt ( Finset.card_le_one.mpr ( by aesop ) ) ( by decide );
        rw [ Finset.card_eq_three ] at h_tu_card; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := h_tu_card; use if x = v then if y = w then z else y else if x = w then if y = v then z else y else if y = v then if z = w then x else z else if y = w then if z = v then x else z else if z = v then if x = w then y else x else if z = w then if x = v then y else x else x; aesop;
      have h_tv : ∃ x, tv = {u, w, x} := by
        have h_tv_card : tv.card = 3 := by
          have h_tv_card : tv ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp htv |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_tv_card |>.2.2;
        have h_tv_contains_u_w : u ∈ tv ∧ w ∈ tv := by
          have h_tv_contains_u_w : (tv ∩ e).card ≥ 2 := by
            have h_tv_inter : (tv ∩ e).card ≥ 2 := by
              have h_inter : tv ∈ trianglesSharingEdge G e := by
                exact Finset.mem_filter.mp htv |>.1
              unfold trianglesSharingEdge at h_inter; aesop;
            exact h_tv_inter;
          grind;
        rw [ Finset.card_eq_three ] at h_tv_card; obtain ⟨ x, y, z, hxyz ⟩ := h_tv_card; use if x = u then if y = w then z else y else if y = u then if x = w then z else x else if z = u then if x = w then y else x else if x = w then y else if y = w then x else z; aesop;
      obtain ⟨x, hx⟩ := h_tu
      obtain ⟨y, hy⟩ := h_tv;
      have := Se_pairwise_intersect G M hM e he tu htu tv htv; simp_all +decide ;
      grind

lemma Se_structure_step2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (u v w : V) (he_eq : e = {u, v, w}) (h_distinct : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (tu : Finset V) (htu : tu ∈ S_e G M e) (hu_tu : u ∉ tu)
    (tv : Finset V) (htv : tv ∈ S_e G M e) (hv_tv : v ∉ tv)
    (tw : Finset V) (htw : tw ∈ S_e G M e) (hw_tw : w ∉ tw)
    (x : V) (hx_not_in_e : x ∉ ({u, v, w} : Finset V))
    (htu_eq : tu = {v, w, x}) (htv_eq : tv = {u, w, x}) :
    tw = {u, v, x} := by
      have htw_uv : u ∈ tw ∧ v ∈ tw := by
        have h_inter : (tw ∩ e).card ≥ 2 := by
          unfold S_e at htw;
          unfold trianglesSharingEdge at htw; aesop;
        have := Finset.one_lt_card.1 h_inter; aesop;
      have htw_vx : v ∈ tw ∧ x ∈ tw := by
        have htw_vx : (tw ∩ tu).card ≥ 2 := by
          exact?;
        contrapose! htw_vx; simp_all +decide [ Finset.inter_comm ] ;
      have htw_card : tw.card = 3 := by
        simp_all +decide [ S_e ];
        simp_all +decide [ trianglesSharingEdge ];
        exact htw.1.card_eq;
      rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ htw_uv.1, Finset.insert_subset_iff.mpr ⟨ htw_uv.2, Finset.singleton_subset_iff.mpr htw_vx.2 ⟩ ⟩ ) ] ; aesop

lemma Se_structure_complete (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_common : ∀ v ∈ e, ∃ t ∈ S_e G M e, v ∉ t) :
    ∃ u v w x, e = {u, v, w} ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ x ∉ e ∧
    S_e G M e ⊆ {e, {v, w, x}, {u, w, x}, {u, v, x}} := by
      obtain ⟨u, v, w, he_eq⟩ : ∃ u v w : V, e = {u, v, w} ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w := by
        have := hM.1;
        rcases this with ⟨ hM₁, hM₂ ⟩;
        have := hM₁ he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rcases this with ⟨ h₁, h₂ ⟩;
        rw [ Finset.card_eq_three ] at h₂; obtain ⟨ u, v, w, h ⟩ := h₂; use u, v, w; aesop;
      obtain ⟨tu, htu, hu_tu⟩ : ∃ tu ∈ S_e G M e, u ∉ tu := h_no_common u (by aesop)
      obtain ⟨tv, htv, hv_tv⟩ : ∃ tv ∈ S_e G M e, v ∉ tv := h_no_common v (by aesop)
      obtain ⟨tw, htw, hw_tw⟩ : ∃ tw ∈ S_e G M e, w ∉ tw := h_no_common w (by aesop)
      obtain ⟨x, hx_not_in_e, htu_eq, htv_eq⟩ : ∃ x, x ∉ ({u, v, w} : Finset V) ∧ tu = {v, w, x} ∧ tv = {u, w, x} := by
        apply Se_structure_step1 G M hM e he u v w he_eq.left he_eq.right tu htu hu_tu tv htv hv_tv
      have htw_eq : tw = {u, v, x} := Se_structure_step2 G M hM e he u v w he_eq.left he_eq.right tu htu hu_tu tv htv hv_tv tw htw hw_tw x hx_not_in_e htu_eq htv_eq;
      refine' ⟨ u, v, w, x, he_eq.1, he_eq.2.1, he_eq.2.2.1, he_eq.2.2.2, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      intro t ht
      by_cases h_cases : t = {u, v, w} ∨ t = {v, w, x} ∨ t = {u, w, x} ∨ t = {u, v, x};
      · exact h_cases;
      · have h_inter : (t ∩ {u, v, w}).card ≥ 2 ∧ (t ∩ {v, w, x}).card ≥ 2 ∧ (t ∩ {u, w, x}).card ≥ 2 ∧ (t ∩ {u, v, x}).card ≥ 2 := by
          have h_inter : ∀ t1 ∈ S_e G M {u, v, w}, ∀ t2 ∈ S_e G M {u, v, w}, (t1 ∩ t2).card ≥ 2 := by
            apply Se_pairwise_intersect G M hM {u, v, w} he;
          exact ⟨ h_inter _ ht _ ( by
            simp +decide [ *, S_e ];
            simp +decide [ trianglesSharingEdge ];
            have := hM.1; simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ] ;
            have := this.2; simp_all +decide [ isTrianglePacking ] ;
            have := ‹M ⊆ G.cliqueFinset 3› he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact fun f hf hf' => ‹ ( M : Set ( Finset V ) ).Pairwise fun t1 t2 => ( t1 ∩ t2 ).card ≤ 1 › hf he hf' |> fun h => by simpa only [ Finset.inter_comm ] using h; ), h_inter _ ht _ htu, h_inter _ ht _ htv, h_inter _ ht _ htw ⟩;
        have h_card : t.card = 3 := by
          have h_card : t ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact h_card.2;
        have h_inter : t ⊆ {u, v, w, x} := by
          intro y hy; contrapose! h_cases; simp_all +decide [ Finset.subset_iff ] ;
          have h_inter : (t ∩ {u, v, w}).card ≤ 2 ∧ (t ∩ {v, w, x}).card ≤ 2 ∧ (t ∩ {u, w, x}).card ≤ 2 ∧ (t ∩ {u, v, x}).card ≤ 2 := by
            exact ⟨ Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ), Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ), Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ), Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ) ⟩;
          grind;
        have h_inter : t = {u, v, w} ∨ t = {u, v, x} ∨ t = {u, w, x} ∨ t = {v, w, x} := by
          have h_subset : t ⊆ {u, v, w, x} := h_inter
          have h_card : t.card = 3 := h_card
          have h_subset : ∀ s : Finset V, s ⊆ {u, v, w, x} → s.card = 3 → s = {u, v, w} ∨ s = {u, v, x} ∨ s = {u, w, x} ∨ s = {v, w, x} := by
            simp +decide [ Finset.subset_iff ];
            intro s hs hs_card
            have h_subset : s ⊆ {u, v, w, x} := by
              exact fun x hx => by simpa using hs hx;
            have h_subset : ∀ s : Finset V, s ⊆ {u, v, w, x} → s.card = 3 → s = {u, v, w} ∨ s = {u, v, x} ∨ s = {u, w, x} ∨ s = {v, w, x} := by
              intro s hs hs_card
              have h_subset : s ⊆ {u, v, w, x} := hs
              have h_card : s.card = 3 := hs_card
              rw [ Finset.card_eq_three ] at h_card;
              rcases h_card with ⟨ a, b, c, hab, hac, hbc, rfl ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
              rcases h_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hab hac hbc ⊢;
            exact h_subset s ‹_› ‹_›;
          exact h_subset t h_inter h_card;
        grind +ring

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  by_cases h_common : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t;
  · exact?;
  · obtain ⟨u, v, w, x, he_eq, h_distinct, hx_not_in_e, hS_e_subset⟩ : ∃ u v w x, e = {u, v, w} ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ x ∉ e ∧ S_e G M e ⊆ {e, {v, w, x}, {u, w, x}, {u, v, x}} := by
      apply_rules [ Se_structure_complete ];
      exact fun v hv => by push_neg at h_common; exact h_common v hv;
    have h_cover : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
      use {Sym2.mk (u, v), Sym2.mk (w, x)};
      simp_all +decide [ Finset.subset_iff ];
      have h_adj_uv : G.Adj u v := by
        have h_adj_uv : {u, v, w} ∈ G.cliqueFinset 3 := by
          have := hM.1;
          exact this.1 he;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        have := h_adj_uv.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have h_adj_wx : G.Adj w x := by
        have h_triangle : {v, w, x} ∈ G.cliqueFinset 3 := by
          have h_triangle : ∃ t ∈ S_e G M {u, v, w}, t = {v, w, x} := by
            grind;
          simp_all +decide [ S_e ];
          unfold trianglesSharingEdge at h_triangle; aesop;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        rw [ SimpleGraph.isNClique_iff ] at h_triangle ; aesop;
      grind;
    unfold triangleCoveringNumberOn;
    obtain ⟨ E', hE'_sub, hE'_card, hE'_cover ⟩ := h_cover; have := Finset.min_le ( show E'.card ∈ Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) from Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩, rfl ⟩ ) ; simp_all +decide ;
    exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M { u, v, w }, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop ) hE'_card

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE-SPECIFIC LEMMAS (TARGET for Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

-- Opposite elements in C4 are vertex-disjoint
lemma cycle_opposite_disjoint (e1 e2 e3 e4 : Finset V)
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34})
    (v41 : V) (hv41 : e4 ∩ e1 = {v41})
    (h_distinct : v12 ≠ v23 ∧ v23 ≠ v34 ∧ v34 ≠ v41 ∧ v41 ≠ v12 ∧ v12 ≠ v34 ∧ v23 ≠ v41)
    (he_cards : e1.card = 3 ∧ e2.card = 3 ∧ e3.card = 3 ∧ e4.card = 3) :
    Disjoint (e1 : Set V) (e3 : Set V) ∧ Disjoint (e2 : Set V) (e4 : Set V) := by
  sorry

-- No bridges between opposite elements
lemma cycle_no_opposite_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e1 e3 : Finset V) (h_disj : Disjoint (e1 : Set V) (e3 : Set V)) :
    X_ef G e1 e3 = ∅ := by
  sorry

-- Main theorem: Cycle configuration (C4 sharing graph)
theorem tau_le_8_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34})
    (v41 : V) (hv41 : e4 ∩ e1 = {v41})
    (h_distinct : v12 ≠ v23 ∧ v23 ≠ v34 ∧ v34 ≠ v41 ∧ v41 ≠ v12 ∧ v12 ≠ v34 ∧ v23 ≠ v41) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

end
