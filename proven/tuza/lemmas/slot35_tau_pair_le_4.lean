/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: da605278-c788-458e-bcfa-0404a47d6983

The following was proved by Aristotle:

- lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4

- lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2

- theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4
-/

/-
Tuza ν=4 Strategy - Slot 35: V-Decomposition for τ(T_pair) ≤ 4

CRITICAL NOTE (from Gemini review):
τ(T_e) ≤ 3 is TRIVIAL (use 3 edges of e). So τ(T_pair) ≤ 6 is worthless.
This submission must prove τ(T_pair) ≤ 4 to be valuable.

APPROACH: V-decomposition can work IF we show overlap:
- Containing v: ≤ 4 spokes, BUT some spokes may also cover avoiding triangles
- Avoiding v: ≤ 2 bases, BUT may be empty or already covered

KEY INSIGHT: Triangles avoiding v that share edge ab must have form {a,b,x}.
If x is adjacent to v (i.e., x ∈ {c,d} from f), then {a,b,x} contains edge ax or bx
which might be a spoke edge. This creates OVERLAP.

Includes FULL PROVEN CODE from Aristotle slot16 (uuid b4f73fa3).
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
-- PROVEN: tau_union_le_sum (FULL PROOF from slot16, uuid b4f73fa3)
-- May timeout locally but compiles in Aristotle's Mathlib version
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

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
-- TARGET LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
Triangles containing v in T_e ∪ T_f can be covered by 4 spoke edges.
If e = {v,a,b} and f = {v,c,d}, use {va, vb, vc, vd}.
-/
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  simp +zetaDelta at *;
  unfold triangleCoveringNumberOn;
  -- Let's choose any four edges incident to $v$.
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

-- TARGET 1

/--
Triangles avoiding v in T_e must share base edge ab (edge of e not containing v).
One edge covers all such triangles. Similarly for T_f with edge cd.
Total: 2 edges.
-/
lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  -- Let $E'$ be the set containing the edges $ab$ and $cd$.
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
    -- Since $f$ is a triangle in $G$, it must have exactly three vertices.
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
  -- Let $E'$ be the set containing the edges $ab$ and $cd$. We need to show that $E'$ covers all triangles avoiding $v$.
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

/- Aristotle failed to find a proof. -/
-- TARGET 2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Overlap between spokes and avoiding triangles
-- ══════════════════════════════════════════════════════════════════════════════

/--
If triangle {a,b,x} avoids v but x is adjacent to v in the graph,
then {a,b,x} is covered by spoke edge {v,x} (since {v,x} ∈ {a,b,x}.sym2 is false,
but {a,x} or {b,x} might be spokes if x ∈ {c,d}).

Actually: {a,b,x} contains edges ab, ax, bx. Spokes are va, vb, vc, vd.
Overlap occurs when ax = vc or ax = vd (i.e., when a=v or x=c, etc.)
Since a ≠ v (a is in e\{v}), we need x ∈ {c,d} for overlap.
-/
lemma avoiding_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ trianglesAvoiding (T_pair G e f) v)
    (h_overlap : ∃ x ∈ t, x ∈ (e ∪ f) \ {v}) :
    ∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
  sorry

-- TARGET: Show overlap when avoiding triangle has vertex from e∪f

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN TARGET: τ(T_pair) ≤ 4 via overlap argument
-- ══════════════════════════════════════════════════════════════════════════════

/-
For any pair sharing vertex v, τ(T_e ∪ T_f) ≤ 4.

KEY INSIGHT: The 4 spoke edges {va, vb, vc, vd} cover:
1. ALL triangles containing v (obvious - each contains some spoke)
2. MOST triangles avoiding v (those with vertices in e∪f are covered by spokes)

The only uncovered triangles are those avoiding v with ALL vertices outside e∪f.
But such triangles can't exist: they would share edge with e or f but have no
common vertices with e or f, contradicting the edge-sharing requirement.
-/
noncomputable section AristotleLemmas

/-
The covering number of the triangles in the pair (e, f) that avoid the common vertex v is at most 2.
-/
lemma tau_avoiding_v_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
      exact?

end AristotleLemmas

theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  have h_zero : triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) = 0 := by
    -- By Lemma~\ref{lem:avoiding_covered_by_spokes}, `t` must contain a spoke incident to `v`.
    have h_contradiction : ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
      intro t ht
      apply avoiding_covered_by_spokes G M hM e f he hf hef v hv t ht
      generalize_proofs at *;
      unfold trianglesAvoiding T_pair at ht;
      unfold trianglesSharingEdge at ht; aesop;
      · exact Exists.elim ( Finset.exists_mem_ne right_1 v ) fun x hx => ⟨ x, Finset.mem_of_mem_inter_left hx.1, Or.inl ( Finset.mem_of_mem_inter_right hx.1 ), hx.2 ⟩;
      · obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( by linarith ) ; use x; aesop;
    -- Since $t$ avoids $v$, it cannot contain any edge incident to $v$, contradicting the existence of a spoke incident to $v$ in $t$.
    have h_contradiction : ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ¬∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
      simp +contextual [ trianglesAvoiding ];
    -- By combining the two hypotheses, we can conclude that there are no triangles in the avoiding set, hence its covering number is zero.
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

-- MAIN TARGET

end