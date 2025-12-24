/-
Tuza ν=4 Portfolio - Slot 29 v2: Triple-Apex Reduction

TARGET: If some vertex v is in ≥3 packing triangles, prove τ ≤ 8

KEY INSIGHT:
When a vertex v appears in 3+ packing elements:
1. Use spoke edges from v to cover all v-containing triangles with ≤4 edges
2. The remaining packing element(s) have ν ≤ 1
3. Apply Parker's bound: τ(T_e) ≤ 2

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

def packingElementsContaining (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  M.filter (fun t => v ∈ t)

def trianglesAtV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (packingElementsContaining M v).biUnion (trianglesSharingEdge G)

def trianglesAtVContainingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∈ t)

def trianglesAtVAvoidingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: tau_union_le_sum (from slot16)
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

  have h_t1_ne_e : t1 ≠ edge_e := by intro heq; rw [heq] at h_disj; rw [Finset.inter_comm] at h_disj; linarith
  have h_t2_ne_e : t2 ≠ edge_e := by intro heq; rw [heq] at h_disj; linarith

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

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  by_cases h_common : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t;
  · exact Se_common_vertex_implies_le_2 G M hM e he h_common
  · -- No common vertex case - structure argument
    -- This follows from Se_structure_complete showing S_e ⊆ K4, then covering K4 with 2 edges
    sorry -- Aristotle will fill this with the full structure proof from slot6

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Triple-Apex Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- When v is in ≥3 packing triangles
theorem tau_le_8_triple_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card ≥ 3) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

-- Specialized version for all 4 sharing v (star)
theorem tau_le_8_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

end
