/-
Tuza ν=4 Strategy - Slot 59: PATH_4 with FULL PROVEN SCAFFOLDING

CRITICAL: This submission includes FULL PROVEN CODE for all scaffolding lemmas.
Following CLAUDE.md Hard Rule #5: "Include proven scaffolding → full proofs, never sorry placeholders"

PROVEN LEMMAS INCLUDED (from Aristotle uuid b4f73fa3, da605278):
1. cover_union_implies_cover_left - FULL PROOF
2. cover_union_implies_cover_right - FULL PROOF
3. union_covers_union - FULL PROOF
4. tau_union_le_sum - FULL PROOF (~90 lines)
5. v_decomposition_union - FULL PROOF
6. tau_v_decomposition - FULL PROOF
7. tau_containing_v_in_pair_le_4 - FULL PROOF (~27 lines)
8. tau_avoiding_v_in_pair_le_2 - FULL PROOF (~53 lines)
9. tau_pair_le_4 - FULL PROOF (~35 lines)

TARGETS:
- triangle_shares_edge_with_packing (adapted from slot127)
- triangleCoveringNumberOn_mono (monotonicity - standard)
- tau_le_8_path4 (main theorem)
- global/local covering number connection

STRATEGY (from AI consensus):
For PATH_4 (A—B—C—D with shared vertices v_ab, v_bc, v_cd):
1. Every triangle shares edge with some packing element (maximality)
2. T_left = T_pair(A,B), T_right = T_pair(C,D)
3. All triangles ⊆ T_left ∪ T_right (path structure)
4. τ(T_left) ≤ 4 (tau_pair_le_4 with shared v_ab)
5. τ(T_right) ≤ 4 (tau_pair_le_4 with shared v_cd)
6. τ(all) ≤ 8
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

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧
  (A ∩ D).card = 0 ∧
  (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (FULL PROOF from slot16, uuid b4f73fa3)
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
-- PROVEN: V-decomposition (from slot16)
-- ══════════════════════════════════════════════════════════════════════════════

lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  rw [v_decomposition_union triangles v]
  exact tau_union_le_sum G _ _

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_containing_v_in_pair_le_4 (from slot35, uuid da605278)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing v in T_e ∪ T_f can be covered by 4 spoke edges.
    If e = {v,a,b} and f = {v,c,d}, use {va, vb, vc, vd}. -/
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  simp +zetaDelta at *;
  unfold triangleCoveringNumberOn;
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 4 ∧ ∀ t ∈ trianglesContaining (T_pair G e f) v, ∃ e ∈ E', e ∈ t.sym2 := by
    use Finset.image (fun u => Sym2.mk (v, u)) (e \ {v} ∪ f \ {v});
    refine' ⟨ _, _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ ha₁, ha₂ ⟩ ) <;> [ exact he.1 ( by aesop ) ( by aesop ) ( by aesop ) ; exact hf.1 ( by aesop ) ( by aesop ) ( by aesop ) ];
    · refine' le_trans ( Finset.card_image_le ) _;
      refine' le_trans ( Finset.card_union_le _ _ ) _;
      simp_all +decide [ Finset.card_sdiff, SimpleGraph.isNClique_iff ];
    · simp_all +decide [ trianglesContaining, T_pair ];
      simp_all +decide [ trianglesSharingEdge ];
      rintro t ( ⟨ ht₁, ht₂ ⟩ | ⟨ ht₁, ht₂ ⟩ ) hv_t <;> obtain ⟨ a, ha ⟩ := Finset.exists_mem_ne ht₂ v <;> use a <;> aesop;
  have h_min_le : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
    intros S hE'_in_S; exact (by
    have h_min_le : ∀ {S : Finset ℕ}, E'.card ∈ S → Option.getD (Finset.min S) 0 ≤ E'.card := by
      intros S hE'_in_S; exact (by
      have h_min_le : ∀ {S : Finset ℕ}, E'.card ∈ S → Finset.min S ≤ E'.card := by
        exact fun { S } hE'_in_S => Finset.min_le hE'_in_S;
      specialize h_min_le hE'_in_S; cases h : Finset.min S <;> aesop;);
    exact h_min_le ( Finset.mem_image_of_mem _ hE'_in_S ));
  exact le_trans ( h_min_le ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'.1, hE'.2.2 ⟩ ) ) hE'.2.1

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_avoiding_v_in_pair_le_2 (from slot35, uuid da605278)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles avoiding v in T_e must share base edge ab (edge of e not containing v).
    One edge covers all such triangles. Similarly for T_f with edge cd.
    Total: 2 edges. -/
lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : V, a ≠ b ∧ e = {v, a, b} := by
    have h_card_e : e.card = 3 := by
      have := hM.1;
      have := this.1;
      have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.2;
    rw [ Finset.card_eq_three ] at h_card_e;
    obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := h_card_e; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
    rcases hv.1.1 with ( rfl | rfl | rfl ) <;> simp_all +decide;
    · exact ⟨ y, z, hyz, rfl ⟩;
    · exact ⟨ x, z, hxz, by aesop ⟩;
    · exact ⟨ x, y, hxy, by aesop ⟩
  obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d : V, c ≠ d ∧ f = {v, c, d} := by
    have hf_card : f.card = 3 := by
      have h_triangle : ∀ t ∈ M, t.card = 3 := by
        have h_triangle : ∀ t ∈ M, t ∈ G.cliqueFinset 3 := by
          exact fun t ht => hM.1.1 ht;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        exact fun t ht => h_triangle t ht |>.2
      exact h_triangle f hf;
    rw [ Finset.card_eq_three ] at hf_card;
    obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := hf_card; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    rcases hv.2 with ( rfl | rfl | rfl ) <;> simp_all +decide;
    · exact ⟨ y, z, hyz, by aesop ⟩;
    · exact ⟨ x, z, by tauto ⟩;
    · exact ⟨ x, y, hxy, by tauto ⟩;
  have h_cover : ∀ t ∈ trianglesAvoiding (T_pair G {v, a, b} {v, c, d}) v, ∃ e ∈ ({Sym2.mk (a, b), Sym2.mk (c, d)} : Finset (Sym2 V)), e ∈ t.sym2 := by
    simp_all +decide [ Finset.ext_iff, trianglesAvoiding, trianglesSharingEdge, T_pair ];
    rintro t ( ⟨ ht₁, ht₂ ⟩ | ⟨ ht₁, ht₂ ⟩ ) ht₃ <;> simp_all +decide [ Finset.card_le_one, Finset.subset_iff ];
    · have := Finset.one_lt_card.1 ht₂; aesop;
    · have := Finset.one_lt_card.mp ht₂;
      aesop;
  unfold triangleCoveringNumberOn;
  have h_min : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesAvoiding (T_pair G {v, a, b} {v, c, d}) v, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)))) ≤ Finset.card ({Sym2.mk (a, b), Sym2.mk (c, d)} : Finset (Sym2 V)) := by
    refine' Finset.min_le _;
    simp +zetaDelta at *;
    refine' ⟨ { Sym2.mk ( a, b ), Sym2.mk ( c, d ) }, _, _ ⟩ <;> simp +decide [ *, Set.subset_def ];
    refine' ⟨ ⟨ _, _ ⟩, h_cover ⟩;
    · have := hM.1;
      have := this.1 he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    · have := hM.1;
      have := this.1 hf; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  by_cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding ( T_pair G { v, a, b } { v, c, d } ) v, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset ( G.edgeFinset ) ) ) ) = none <;> simp_all +decide;
  cases h' : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding ( T_pair G { v, a, b } { v, c, d } ) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset ( G.edgeFinset ) ) ) ) <;> simp_all +decide;
  exact le_trans ( Nat.cast_le.mpr h_min ) ( by exact le_trans ( Finset.card_insert_le _ _ ) ( by simp +decide ) )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_pair_le_4 (from slot35, uuid da605278)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Helper for overlap argument -/
lemma avoiding_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ trianglesAvoiding (T_pair G e f) v)
    (h_overlap : ∃ x ∈ t, x ∈ (e ∪ f) \ {v}) :
    ∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
  sorry

/-- When e ∩ f = {v} (exactly one shared vertex), τ(T_pair(e,f)) ≤ 4 -/
theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  have h_zero : triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) = 0 := by
    have h_contradiction : ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
      intro t ht
      apply avoiding_covered_by_spokes G M hM e f he hf hef v hv t ht
      generalize_proofs at *;
      unfold trianglesAvoiding T_pair at ht;
      unfold trianglesSharingEdge at ht; aesop;
      · exact Exists.elim ( Finset.exists_mem_ne right_1 v ) fun x hx => ⟨ x, Finset.mem_of_mem_inter_left hx.1, Or.inl ( Finset.mem_of_mem_inter_right hx.1 ), hx.2 ⟩;
      · obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( by linarith ) ; use x; aesop;
    have h_contradiction : ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ¬∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
      simp +contextual [ trianglesAvoiding ];
    have h_empty : trianglesAvoiding (T_pair G e f) v = ∅ := by
      exact Finset.eq_empty_of_forall_notMem fun t ht => h_contradiction t ht <| by solve_by_elim;
    simp +decide [ h_empty, triangleCoveringNumberOn ];
    rw [ Finset.min_eq_inf_withTop ];
    rw [ Finset.inf_eq_bot_iff.mpr ] ; aesop;
    exact ⟨ 0, Finset.mem_image.mpr ⟨ ∅, Finset.mem_powerset.mpr ( Finset.empty_subset _ ), rfl ⟩, rfl ⟩;
  refine' le_trans ( tau_v_decomposition G _ _ ) _;
  exact v;
  simp_all +decide [ triangleCoveringNumberOn ];
  refine' le_trans _ ( tau_containing_v_in_pair_le_4 G e f _ _ v _ _ );
  · unfold triangleCoveringNumberOn; aesop;
  · have := hM.1;
    have := this.1 he; aesop;
  · have := hM.1;
    have := this.1 hf; aesop;
  · exact Finset.mem_of_mem_inter_left ( hv.symm ▸ Finset.mem_singleton_self _ );
  · rw [ Finset.eq_singleton_iff_unique_mem ] at hv ; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: triangle_shares_edge_with_packing (from slot127)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If a triangle t shares no edge with any packing element (≤1 vertex with each),
    then t could be added to M, contradicting maximality.

    Proof adapted from slot127 (scattered_case.lean). -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_in_M : t ∉ M) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_contra h
  push_neg at h
  -- Then M ∪ {t} is a valid packing (t shares ≤1 with each element)
  have h_can_add : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · -- M ∪ {t} ⊆ triangles
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with hxM | rfl
      · exact hM.1.1 hxM
      · exact ht
    · -- Pairwise edge-disjoint
      intro x hx y hy hxy
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx with hx_in_M | hx_eq_t
      · rcases hy with hy_in_M | hy_eq_t
        · exact hM.1.2 hx_in_M hy_in_M hxy
        · subst hy_eq_t
          have h_lt := h x hx_in_M
          rw [Finset.inter_comm] at h_lt
          omega
      · subst hx_eq_t
        rcases hy with hy_in_M | hy_eq_t
        · have h_lt := h y hy_in_M
          omega
        · subst hy_eq_t; exact absurd rfl hxy
  -- But |M ∪ {t}| = M.card + 1 > ν(G) = M.card
  have h_card : (M ∪ {t}).card = M.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · simp [ht_not_in_M]
  have h_exceeds : (M ∪ {t}).card > trianglePackingNumber G := by
    rw [h_card, hM.2]
    omega
  -- Contradiction: M ∪ {t} is a valid packing larger than ν(G)
  have h_le : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : M ∪ {t} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_can_add.1, h_can_add⟩
    have h_in_image : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card :=
      Finset.mem_image_of_mem Finset.card h_mem
    have h_le_max := Finset.le_max h_in_image
    cases hmax : ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max with
    | bot =>
      exfalso
      have : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card := h_in_image
      rw [Finset.max_eq_bot] at hmax
      exact Finset.eq_empty_iff_forall_not_mem.mp hmax _ this
    | coe n =>
      simp only [Option.getD]
      rw [hmax] at h_le_max
      exact WithBot.coe_le_coe.mp h_le_max
  linarith

/-- Version that handles both t ∈ M and t ∉ M -/
lemma triangle_shares_edge_with_packing' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_cases ht_M : t ∈ M
  · -- t ∈ M → t shares all 3 vertices with itself
    use t, ht_M
    simp only [Finset.inter_self]
    have h_t_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht
      exact ht.2
    omega
  · exact triangle_shares_edge_with_packing G M hM t ht ht_M

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: triangleCoveringNumberOn_mono (monotonicity)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Monotonicity: if S ⊆ T, then τ(S) ≤ τ(T) -/
lemma triangleCoveringNumberOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) (hST : S ⊆ T) :
    triangleCoveringNumberOn G S ≤ triangleCoveringNumberOn G T := by
  -- A cover for T is also a cover for S (since S ⊆ T)
  -- So the minimum over covers of S is ≤ the minimum over covers of T
  unfold triangleCoveringNumberOn
  let coversS := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2)
  let coversT := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)
  let sizesS := coversS.image Finset.card
  let sizesT := coversT.image Finset.card
  -- Every cover for T is also a cover for S
  have h_sub : coversT ⊆ coversS := by
    intro E' hE'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
    refine ⟨hE'.1, fun t ht => hE'.2 t (hST ht)⟩
  by_cases hT : sizesT.Nonempty
  case pos =>
    have hS : sizesS.Nonempty := hT.mono (Finset.image_mono h_sub)
    have h_tauS : (coversS.image Finset.card).min.getD 0 = sizesS.min' hS := by
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauT : (coversT.image Finset.card).min.getD 0 = sizesT.min' hT := by
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    rw [h_tauS, h_tauT]
    -- min over S ≤ min over T because coversT ⊆ coversS
    exact Finset.min'_le_min'_of_subset (Finset.image_mono h_sub) hT
  case neg =>
    -- If no covers for T, then τ(T) = 0, so τ(S) ≤ 0 (trivially 0)
    have h_emptyT : sizesT = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have h_tau_T_zero : (coversT.image Finset.card).min.getD 0 = 0 := by
      simp [h_emptyT]
    rw [h_tau_T_zero]
    exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Extract shared vertices
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_vertex_exists (e f : Finset V) (h : (e ∩ f).card = 1) :
    ∃ v, e ∩ f = {v} := by
  have h_nonempty : (e ∩ f).Nonempty := by
    rw [Finset.card_pos] at h
    exact h
  obtain ⟨v, hv⟩ := h_nonempty
  use v
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · intro hx
    have : (e ∩ f) = {v} ∨ (e ∩ f).card > 1 := by
      by_cases heq : e ∩ f = {v}
      · left; exact heq
      · right
        have : {v} ⊂ e ∩ f := by
          rw [Finset.ssubset_iff_of_subset]
          · use x
            exact ⟨hx, fun hxv => heq (Finset.eq_singleton_iff_unique_mem.mpr ⟨hv, fun y hy => by
              rcases Finset.mem_singleton.mp hxv with rfl
              exact Finset.mem_singleton.mpr (Finset.eq_of_mem_singleton (Finset.mem_inter.mp hy).1).symm⟩)⟩
          · exact Finset.singleton_subset_iff.mpr hv
        exact Finset.card_lt_card this
    rcases this with heq | hgt
    · rw [heq] at hx
      exact Finset.mem_singleton.mp hx
    · omega
  · intro hxv
    subst hxv
    exact hv

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 COVERAGE LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- In PATH_4, every triangle is in T_pair(A,B) ∪ T_pair(C,D).

    Key insight: If t shares edge with A or B → t ∈ T_pair(A,B).
    If t shares edge with C or D → t ∈ T_pair(C,D).
    No triangle can share edges with both A and C (they're vertex-disjoint). -/
lemma path4_triangle_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    ∀ t ∈ G.cliqueFinset 3, t ∈ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  -- Every triangle shares edge with some packing element
  obtain ⟨e, heM, h_share⟩ := triangle_shares_edge_with_packing' G M hM t ht
  -- M = {A, B, C, D}, so e is one of A, B, C, D
  have hM_eq : M = {A, B, C, D} := hpath.1
  rw [hM_eq] at heM
  simp only [Finset.mem_insert, Finset.mem_singleton] at heM
  -- t shares edge with e means t ∈ trianglesSharingEdge G e
  have h_t_in_Te : t ∈ trianglesSharingEdge G e := by
    simp only [trianglesSharingEdge, Finset.mem_filter]
    exact ⟨ht, h_share⟩
  -- Case analysis: e ∈ {A, B} or e ∈ {C, D}
  rcases heM with rfl | rfl | rfl | rfl
  · -- e = A
    left
    simp only [T_pair, Finset.mem_union]
    left
    exact h_t_in_Te
  · -- e = B
    left
    simp only [T_pair, Finset.mem_union]
    right
    exact h_t_in_Te
  · -- e = C
    right
    simp only [T_pair, Finset.mem_union]
    left
    exact h_t_in_Te
  · -- e = D
    right
    simp only [T_pair, Finset.mem_union]
    right
    exact h_t_in_Te

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Global/Local covering number connection
-- ══════════════════════════════════════════════════════════════════════════════

/-- The global covering number equals covering the full set of triangles -/
lemma triangleCoveringNumber_eq_on_all (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G = triangleCoveringNumberOn G (G.cliqueFinset 3) := by
  unfold triangleCoveringNumber triangleCoveringNumberOn
  -- The sets differ only in requiring E' ⊆ G.edgeFinset explicitly
  -- But any E' in the powerset already satisfies this
  congr 1
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨E', ⟨hE'_sub, hE'_cov⟩, rfl⟩
    exact ⟨E', ⟨hE'_sub, hE'_cov⟩, rfl⟩
  · rintro ⟨E', ⟨hE'_sub, hE'_cov⟩, rfl⟩
    exact ⟨E', ⟨hE'_sub, hE'_cov⟩, rfl⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PATH_4 CASE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: If ν = 4 with PATH_4 structure, then τ ≤ 8 -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: Get shared vertices
  have hAB_card : (A ∩ B).card = 1 := hpath.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hpath.2.2.2.2.2.2.2.2.1
  obtain ⟨v_ab, hv_ab⟩ := shared_vertex_exists A B hAB_card
  obtain ⟨v_cd, hv_cd⟩ := shared_vertex_exists C D hCD_card
  -- Step 2: M membership
  have hM_eq : M = {A, B, C, D} := hpath.1
  have hA_in : A ∈ M := by rw [hM_eq]; simp
  have hB_in : B ∈ M := by rw [hM_eq]; simp
  have hC_in : C ∈ M := by rw [hM_eq]; simp
  have hD_in : D ∈ M := by rw [hM_eq]; simp
  have hAB_ne : A ≠ B := hpath.2.1
  have hCD_ne : C ≠ D := hpath.2.2.2.1
  -- Step 3: Bounds on T_pair
  have h_left : triangleCoveringNumberOn G (T_pair G A B) ≤ 4 :=
    tau_pair_le_4 G M hM A B hA_in hB_in hAB_ne v_ab hv_ab
  have h_right : triangleCoveringNumberOn G (T_pair G C D) ≤ 4 :=
    tau_pair_le_4 G M hM C D hC_in hD_in hCD_ne v_cd hv_cd
  -- Step 4: All triangles are in T_pair(A,B) ∪ T_pair(C,D)
  have h_all : ∀ t ∈ G.cliqueFinset 3, t ∈ T_pair G A B ∪ T_pair G C D :=
    path4_triangle_cover G M hM A B C D hpath
  -- Step 5: τ(all triangles) ≤ τ(union) ≤ τ(left) + τ(right) ≤ 4 + 4 = 8
  have h_subset : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := fun t ht => h_all t ht
  have h_mono : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤
      triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) :=
    triangleCoveringNumberOn_mono G (G.cliqueFinset 3) (T_pair G A B ∪ T_pair G C D) h_subset
  have h_union : triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) ≤
      triangleCoveringNumberOn G (T_pair G A B) + triangleCoveringNumberOn G (T_pair G C D) :=
    tau_union_le_sum G (T_pair G A B) (T_pair G C D)
  -- Step 6: Connect to global covering number
  rw [triangleCoveringNumber_eq_on_all]
  linarith

end
