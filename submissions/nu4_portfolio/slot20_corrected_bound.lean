/-
Tuza ν=4 Portfolio - Slot 20: Corrected Bound τ(T_e ∪ T_f) ≤ 6

CRITICAL FIXES FROM ANALYSIS:
1. `tau_containing_vertex_le_2` is FALSE - correct bound is ≤ 4
2. `avoiding_v_vertices` is FALSE - vertices can be outside (e\{v}) ∪ (f\{v})
3. BUT: τ(avoiding v in T_e) ≤ 1 IS TRUE (proven)

CORRECTED STRATEGY:
- τ(containing v in T_e ∪ T_f) ≤ 4 (4 spokes: v-u, v-w, v-x, v-y)
- τ(avoiding v in T_e) ≤ 1 (edge e\{v})
- τ(avoiding v in T_f) ≤ 1 (edge f\{v})
- Total: τ(T_e ∪ T_f) ≤ 6
-/

import Mathlib

set_option maxHeartbeats 800000

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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: isTriangleCover helper definitions and lemmas (PROVEN in slot18)
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (C : Finset (Sym2 V)) : Prop :=
  C ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ C, e ∈ t.sym2

lemma isTriangleCover_union {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset (Finset V)} {CA CB : Finset (Sym2 V)}
    (hA : isTriangleCover G A CA) (hB : isTriangleCover G B CB) :
    isTriangleCover G (A ∪ B) (CA ∪ CB) := by
      constructor <;> simp_all +decide;
      · cases hA ; cases hB ; aesop;
      · rintro t ( ht | ht );
        · rcases hA with ⟨ hA₁, hA₂ ⟩ ; specialize hA₂ t ht ; aesop;
        · rcases hB.2 t ht with ⟨ e, he, he' ⟩ ; use e ; aesop

lemma le_card_of_isTriangleCover {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)} {C : Finset (Sym2 V)}
    (h : isTriangleCover G A C) :
    triangleCoveringNumberOn G A ≤ C.card := by
      refine' le_trans _ _;
      exact ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) |> Finset.image Finset.card |> Finset.min |> fun x => x.getD 0 );
      · bound;
      · have hC' : C ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (G.edgeFinset.powerset) := by
          unfold isTriangleCover at h; aesop;
        have hC'' : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (G.edgeFinset.powerset))) ≤ Finset.card C := by
          exact Finset.min_le ( Finset.mem_image_of_mem _ hC' );
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( G.edgeFinset.powerset ) ) ) <;> aesop

lemma exists_min_isTriangleCover {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)}
    (h : ∃ C, isTriangleCover G A C) :
    ∃ C, isTriangleCover G A C ∧ C.card = triangleCoveringNumberOn G A := by
      unfold triangleCoveringNumberOn;
      obtain ⟨ C, hC ⟩ := h;
      have h_min : ∃ C ∈ G.edgeFinset.powerset, (∀ t ∈ A, ∃ e ∈ C, e ∈ t.sym2) ∧ ∀ C' ∈ G.edgeFinset.powerset, (∀ t ∈ A, ∃ e ∈ C', e ∈ t.sym2) → C.card ≤ C'.card := by
        have h_min : ∃ C ∈ Finset.filter (fun C => ∀ t ∈ A, ∃ e ∈ C, e ∈ t.sym2) (G.edgeFinset.powerset), ∀ C' ∈ Finset.filter (fun C => ∀ t ∈ A, ∃ e ∈ C, e ∈ t.sym2) (G.edgeFinset.powerset), C.card ≤ C'.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ C, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hC.1, hC.2 ⟩ ⟩;
        exact ⟨ h_min.choose, Finset.mem_filter.mp h_min.choose_spec.1 |>.1, Finset.mem_filter.mp h_min.choose_spec.1 |>.2, fun C' hC' hC'' => h_min.choose_spec.2 C' ( Finset.mem_filter.mpr ⟨ hC', hC'' ⟩ ) ⟩;
      obtain ⟨ C, hC₁, hC₂, hC₃ ⟩ := h_min;
      refine' ⟨ C, ⟨ Finset.mem_powerset.mp hC₁, hC₂ ⟩, _ ⟩;
      have h_min_card : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset))) = some C.card := by
        refine' le_antisymm _ _;
        · exact Finset.min_le ( Finset.mem_image.mpr ⟨ C, by aesop ⟩ );
        · simp +decide [ Finset.min ];
          exact fun b hb₁ hb₂ => WithTop.coe_le_coe.mpr ( hC₃ b ( Finset.mem_powerset.mpr ( by simpa [ Finset.subset_iff, Set.subset_def ] using hb₁ ) ) ( by simpa [ Finset.subset_iff, Set.subset_def ] using hb₂ ) );
      exact h_min_card.symm ▸ rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot16, uuid b4f73fa3)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ C, isTriangleCover G A C
  by_cases hB : ∃ C, isTriangleCover G B C;
  · obtain ⟨CA, hCA⟩ := exists_min_isTriangleCover hA
    obtain ⟨CB, hCB⟩ := exists_min_isTriangleCover hB;
    exact le_trans ( le_card_of_isTriangleCover ( isTriangleCover_union hCA.1 hCB.1 ) ) ( by rw [ ← hCA.2, ← hCB.2 ] ; exact Finset.card_union_le _ _ );
  · have h_union_not_coverable : ¬∃ C, isTriangleCover G (A ∪ B) C := by
      rintro ⟨ C, hC ⟩;
      exact hB ⟨ C, hC.1, fun t ht => hC.2 t ( Finset.mem_union_right _ ht ) ⟩;
    unfold triangleCoveringNumberOn;
    rw [ show ( Finset.filter ( fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E hE => h_union_not_coverable ⟨ E, Finset.mem_powerset.mp ( Finset.mem_filter.mp hE |>.1 ), Finset.mem_filter.mp hE |>.2 ⟩ ] ; simp +decide;
    exact Nat.zero_le _;
  · have h_not_coverable : ¬∃ C, isTriangleCover G (A ∪ B) C := by
      contrapose! hA;
      exact ⟨ hA.choose, ⟨ hA.choose_spec.1, fun t ht => hA.choose_spec.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩;
    have h_min_zero : triangleCoveringNumberOn G (A ∪ B) = 0 := by
      unfold triangleCoveringNumberOn;
      simp +zetaDelta at *;
      rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) = ∅ from ?_ ] ; simp +decide;
      simp_all +decide [ isTriangleCover ];
    grind

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_avoiding_le_1 (from slot18, uuid 0e54e1a7)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_avoiding_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (v : V) (he : e ∈ G.cliqueFinset 3) (hv : v ∈ e) :
    triangleCoveringNumberOn G (trianglesAvoiding (trianglesSharingEdge G e) v) ≤ 1 := by
      unfold triangleCoveringNumberOn;
      obtain ⟨u, w, hu⟩ : ∃ u w : V, u ≠ w ∧ e = {v, u, w} := by
        simp_all +decide [ Finset.card_eq_three, Finset.mem_powerset, Finset.mem_filter ];
        rcases Finset.card_eq_three.mp he.2 with ⟨ u, w, x, hu, hw, hx, h ⟩ ; use if u = v then w else if w = v then x else u, if u = v then x else if w = v then u else w ; aesop;
      have h_edge_ϵ : ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G e) v, (Sym2.mk (u, w)) ∈ t.sym2 := by
        intro t ht
        have h_inter : (t ∩ e).card ≥ 2 := by
          unfold trianglesAvoiding trianglesSharingEdge at ht; aesop;
        have h_inter_eq : t ∩ e = {u, w} := by
          have h_inter_eq : t ∩ e ⊆ {u, w} := by
            unfold trianglesAvoiding at ht; aesop;
          exact Finset.eq_of_subset_of_card_le h_inter_eq ( by rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop );
        simp_all +decide [ Finset.ext_iff, Sym2.mem_iff ];
        exact ⟨ by specialize h_inter_eq u; aesop, by specialize h_inter_eq w; aesop ⟩;
      have h_image : 1 ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G e) v, ∃ e ∈ E', e ∈ t.sym2}) := by
        simp +zetaDelta at *;
        use {Sym2.mk (u, w)};
        simp_all +decide [ SimpleGraph.isNClique_iff ];
      have h_min : ∀ {S : Finset ℕ}, 1 ∈ S → Finset.min S ≤ 1 := by
        exact fun { S } hS => Finset.min_le hS;
      convert h_min h_image using 1;
      cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding ( trianglesSharingEdge G e ) v, ∃ e ∈ E', e ∈ t.sym2 } ) ) <;> simp +decide [ h ];
      · exact absurd h ( ne_of_lt ( lt_of_le_of_lt ( Finset.min_le h_image ) ( WithTop.coe_lt_top _ ) ) );
      · rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- V-DECOMPOSITION (follows from tau_union_le_sum)
-- ══════════════════════════════════════════════════════════════════════════════

lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t; simp [trianglesContaining, trianglesAvoiding]; tauto

theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  rw [v_decomposition_union triangles v]
  exact tau_union_le_sum G _ _

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY NEW LEMMA: τ(containing v) ≤ 4 for T_e ∪ T_f
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ(containing v in T_e ∪ T_f) ≤ 4 when e ∩ f = {v}
    Proof idea: triangles containing v share one of 4 edges with e or f:
    (v,u), (v,w) from e = {v,u,w} or (v,x), (v,y) from f = {v,x,y}
    Each group can be covered by 1 edge. -/
lemma tau_containing_v_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G
      (trianglesContaining (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) v) ≤ 4 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY NEW LEMMA: τ(avoiding v) ≤ 2 for T_e ∪ T_f
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ(avoiding v in T_e ∪ T_f) ≤ 2
    Uses: τ(avoiding v in T_e) ≤ 1 and τ(avoiding v in T_f) ≤ 1 -/
lemma tau_avoiding_v_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G
      (trianglesAvoiding (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) v) ≤ 2 := by
  have h_e_tri : e ∈ G.cliqueFinset 3 := hM.1.1 he
  have h_f_tri : f ∈ G.cliqueFinset 3 := hM.1.1 hf
  have h_v_in_e : v ∈ e := Finset.mem_of_mem_inter_left (h_inter.symm ▸ Finset.mem_singleton_self v)
  have h_v_in_f : v ∈ f := Finset.mem_of_mem_inter_right (h_inter.symm ▸ Finset.mem_singleton_self v)
  -- trianglesAvoiding (T_e ∪ T_f) v ⊆ trianglesAvoiding T_e v ∪ trianglesAvoiding T_f v
  have h_subset : trianglesAvoiding (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) v ⊆
      trianglesAvoiding (trianglesSharingEdge G e) v ∪ trianglesAvoiding (trianglesSharingEdge G f) v := by
    intro t ht
    simp only [trianglesAvoiding, Finset.mem_filter, Finset.mem_union] at ht ⊢
    obtain ⟨ht_mem, ht_notin⟩ := ht
    rcases ht_mem with h_in_e | h_in_f
    · left; exact ⟨h_in_e, ht_notin⟩
    · right; exact ⟨h_in_f, ht_notin⟩
  -- Use tau_union_le_sum and tau_avoiding_le_1
  calc triangleCoveringNumberOn G (trianglesAvoiding (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) v)
      ≤ triangleCoveringNumberOn G (trianglesAvoiding (trianglesSharingEdge G e) v ∪
          trianglesAvoiding (trianglesSharingEdge G f) v) := by
        sorry -- monotonicity: smaller set has smaller covering number
    _ ≤ triangleCoveringNumberOn G (trianglesAvoiding (trianglesSharingEdge G e) v) +
        triangleCoveringNumberOn G (trianglesAvoiding (trianglesSharingEdge G f) v) :=
        tau_union_le_sum G _ _
    _ ≤ 1 + 1 := Nat.add_le_add (tau_avoiding_le_1 G e v h_e_tri h_v_in_e)
                                (tau_avoiding_le_1 G f v h_f_tri h_v_in_f)
    _ = 2 := by ring

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ(T_e ∪ T_f) ≤ 6
-- ══════════════════════════════════════════════════════════════════════════════

/-- CORRECTED: τ(T_e ∪ T_f) ≤ 6 when e ∩ f = {v} (not 4 as previously claimed) -/
theorem tau_pair_le_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 6 := by
  let T_ef := trianglesSharingEdge G e ∪ trianglesSharingEdge G f
  calc triangleCoveringNumberOn G T_ef
      ≤ triangleCoveringNumberOn G (trianglesContaining T_ef v) +
        triangleCoveringNumberOn G (trianglesAvoiding T_ef v) := tau_v_decomposition G T_ef v
    _ ≤ 4 + 2 := Nat.add_le_add (tau_containing_v_le_4 G M hM e f he hf hef v h_inter)
                                (tau_avoiding_v_le_2 G M hM e f he hf hef v h_inter)
    _ = 6 := by ring

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: τ ≤ 12 for ν = 4 (weaker but achievable bound)
-- ══════════════════════════════════════════════════════════════════════════════

/-- For ν=4, τ ≤ 12 using pairwise bounds -/
theorem tuza_nu4_weak (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 12 := by
  sorry

end
