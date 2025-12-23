/-
Tuza ν=4 Portfolio - Slot 15: V-Decomposition with Parker Scaffolding

TARGET: Prove τ(T_e ∪ T_f) ≤ 4 using vertex decomposition

SCAFFOLDING: Full proofs from parker_lemmas.lean included to prevent re-proving.
Key proven lemma: covering_number_on_le_two_of_subset_four (triangles on ≤4 vertices have τ ≤ 2)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from Parker)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- V-DECOMPOSITION DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from parker_lemmas.lean)
-- ══════════════════════════════════════════════════════════════════════════════

-- Helper lemma from Parker (FULL PROOF)
lemma covering_number_le_two_of_subset_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.card ≤ 4)
    (h_subset : ∀ t ∈ G.cliqueFinset 3, t ⊆ U) :
    triangleCoveringNumber G ≤ 2 := by
  have h_cover : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 2 := by
    have h_triangles : ∃ E' : Finset (Sym2 V), E' ⊆ Finset.image (fun e => Sym2.mk e) (Finset.offDiag U) ∧ (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 2 := by
      obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ Finset.image (fun e => Sym2.mk e) (Finset.offDiag U) ∧ E'.card ≤ 2 ∧ ∀ t ∈ Finset.powersetCard 3 U, t.card = 3 → ∃ e ∈ E', e ∈ t.sym2 := by
        interval_cases _ : U.card <;> simp_all +decide;
        · exact ⟨ ∅, by simp +decide, by simp +decide, by intros; linarith [ Finset.card_le_card ‹_› ] ⟩;
        · exact ⟨ ∅, by simp +decide, by simp +decide, by intros; exact absurd ( Finset.card_le_card ‹_› ) ( by simp +decide [ * ] ) ⟩;
        · rw [ Finset.card_eq_three ] at *;
          obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := ‹∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ U = { x, y, z } ›; use { Sym2.mk ( x, y ), Sym2.mk ( x, z ) } ; simp_all +decide ;
          simp_all +decide [ Finset.subset_iff ];
          exact ⟨ ⟨ ⟨ x, y, by aesop ⟩, ⟨ x, z, by aesop ⟩ ⟩, fun t ht ht' => by rw [ Finset.card_eq_three ] at ht'; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := ht'; aesop ⟩;
        · obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ : ∃ a b c d : V, a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ d ∈ U ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ U = {a, b, c, d} := by
            simp_rw +decide [ Finset.card_eq_succ ] at *;
            rcases ‹_› with ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ ; use a, b, c, d; aesop;
          refine' ⟨ { Sym2.mk ( a, b ), Sym2.mk ( c, d ) }, _, _, _ ⟩ <;> simp_all +decide;
          · simp +decide [ Finset.insert_subset_iff, habcd ];
            exact ⟨ ⟨ a, b, by aesop ⟩, ⟨ c, d, by aesop ⟩ ⟩;
          · intro t ht ht'; have := Finset.card_eq_three.mp ht'; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
            grind;
      refine' ⟨ E', hE'.1, _, hE'.2.1 ⟩;
      intro t ht; specialize hE' ; specialize h_subset t ht; aesop;
      exact right t h_subset ht.card_eq;
    obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_triangles; use E' ∩ G.edgeFinset; aesop;
    · obtain ⟨ e, he₁, he₂ ⟩ := hE₂ t a; use e; aesop;
      have := hE₁ he₁; aesop;
      exact a.1 ( by aesop ) ( by aesop ) ( by aesop );
    · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) hE₃;
  obtain ⟨ E', hE'₁, hE'₂, hE'₃ ⟩ := h_cover; refine' le_trans _ hE'₃; simp +decide [ triangleCoveringNumber ] ; aesop;
  have h_min : (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)).min ≤ E'.card := by
    refine' Finset.min_le _ ; aesop;
    refine' ⟨ E', ⟨ hE'₁, ⟨ _, _ ⟩ ⟩, rfl ⟩ <;> aesop;
  cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop

-- KEY LEMMA: Triangles on ≤4 vertices have τ ≤ 2 (FULL PROOF from Parker)
lemma covering_number_on_le_two_of_subset_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (U : Finset V) (hU : U.card ≤ 4) (h_subset : ∀ t ∈ S, t ⊆ U) :
    triangleCoveringNumberOn G S ≤ 2 := by
  have h_exists_cover : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 2 := by
    set G' : SimpleGraph V := SimpleGraph.fromRel (fun v w => ∃ t ∈ S, {v, w} ⊆ t);
    have h_covering_number_G' : ∃ E' : Finset (Sym2 V), E' ⊆ G'.edgeFinset ∧ (∀ t ∈ G'.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 2 := by
      have h_covering_number_G' : ∀ t ∈ G'.cliqueFinset 3, t ⊆ U := by
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        intro t ht;
        have := ht.1; aesop;
        intro v hv;
        obtain ⟨ w, hw, hw' ⟩ := Finset.exists_mem_ne ( show 1 < Finset.card t from by linarith [ ht.2 ] ) v;
        have := this hv hw; aesop;
        rcases this ( Ne.symm hw' ) with ( ⟨ t, ht, ht' ⟩ | ⟨ t, ht, ht' ⟩ ) <;> have := h_subset t ht <;> simp_all +decide [ Finset.subset_iff ];
      have h_covering_number_G' : triangleCoveringNumber G' ≤ 2 := by
        exact covering_number_le_two_of_subset_four G' U hU h_covering_number_G';
      unfold triangleCoveringNumber at h_covering_number_G';
      by_cases h : Finset.Nonempty ( Finset.filter ( isTriangleCover G' ) G'.edgeFinset.powerset ) <;> simp_all +decide [ Finset.min ];
      · have := Finset.exists_min_image _ ( fun x => Finset.card x ) h;
        obtain ⟨ E', hE', hE'' ⟩ := this;
        use E';
        aesop;
        · have := right.2 t; aesop;
        · contrapose! h_covering_number_G';
          rw [ Finset.inf_eq_iInf ];
          rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
          rotate_left;
          exact ↑E'.card;
          · intro i; rw [ ciInf_eq_ite ] ; aesop;
          · intro w hw;
            use E';
            rw [ ciInf_eq_ite ] ; aesop;
          · exact h_covering_number_G';
      · contrapose! h;
        refine' ⟨ G'.edgeFinset, _, _ ⟩ <;> simp +decide [ isTriangleCover ];
        intro t ht; have := ht.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        rcases Finset.card_eq_three.mp this with ⟨ a, b, c, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
    obtain ⟨ E', hE'₁, hE'₂, hE'₃ ⟩ := h_covering_number_G'; use E'; aesop;
    · intro e he; specialize hE'₁ he; aesop;
      rcases e with ⟨ v, w ⟩ ; simp_all +decide [ SimpleGraph.fromRel ] ;
      rcases hE'₁.2 with ( ⟨ t, ht, h ⟩ | ⟨ t, ht, h ⟩ ) <;> have := hS ht <;> simp_all +decide [ Finset.subset_iff ];
      · have := hS ht; rw [ SimpleGraph.isNClique_iff ] at this; aesop;
      · have := hS ht; rw [ SimpleGraph.isNClique_iff ] at this; aesop;
    · apply hE'₂ t;
      have := hS a; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      intro v hv w hw; aesop;
      exact Or.inl ⟨ t, a, by aesop_cat ⟩;
  unfold triangleCoveringNumberOn; aesop;
  unfold Option.getD; aesop;
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card ( show w ∈ Finset.filter ( fun E' => ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) from Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by aesop_cat ), left_1 ⟩ ) ) ; aesop;
  exact Nat.cast_le.mp ( le_trans this ( WithTop.coe_le_coe.mpr right ) )

-- ══════════════════════════════════════════════════════════════════════════════
-- GAPS TO FILL (Aristotle should focus here)
-- ══════════════════════════════════════════════════════════════════════════════

-- Z has vertices only in (e \ {v}) ∪ (f \ {v}) which has ≤4 vertices
lemma avoiding_v_vertices (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) (v : V)
    (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v})
    (triangles : Finset (Finset V))
    (h_sub : triangles ⊆ trianglesSharingEdge G e ∪ trianglesSharingEdge G f)
    (h_avoid : ∀ t ∈ triangles, v ∉ t) :
    (triangles.biUnion id) ⊆ (e \ {v}) ∪ (f \ {v}) := by
  sorry

-- (e \ {v}) ∪ (f \ {v}) has exactly 4 vertices when e ∩ f = {v}
lemma non_v_vertices_card (e f : Finset V) (v : V)
    (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v})
    (h_disjoint : (e \ {v}) ∩ (f \ {v}) = ∅) :
    ((e \ {v}) ∪ (f \ {v})).card = 4 := by
  sorry

-- Triangles containing v can be covered by 2 edges incident to v
lemma containing_v_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V)
    (h_cliques : triangles ⊆ G.cliqueFinset 3)
    (h_contain : ∀ t ∈ triangles, v ∈ t) :
    triangleCoveringNumberOn G triangles ≤ 2 := by
  sorry

-- The union splits into Y_v and Z
lemma v_decomposition (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

-- Covering number of union bounded by sum
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: τ(T_e ∪ T_f) ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  let T_ef := trianglesSharingEdge G e ∪ trianglesSharingEdge G f
  let Y_v := trianglesContaining T_ef v
  let Z := trianglesAvoiding T_ef v
  have h_decomp : T_ef = Y_v ∪ Z := v_decomposition T_ef v
  -- τ(Y_v) ≤ 2: all triangles in Y_v contain v
  have h_Yv_bound : triangleCoveringNumberOn G Y_v ≤ 2 := by
    apply containing_v_cover
    · intro t ht
      simp [Y_v, trianglesContaining, T_ef] at ht
      rcases ht with ⟨⟨h1, _⟩ | ⟨h1, _⟩, _⟩
      · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h1).1
    · intro t ht
      simp [Y_v, trianglesContaining] at ht
      exact ht.2
  -- τ(Z) ≤ 2: Z lives on ≤4 vertices, apply proven scaffolding
  have h_Z_bound : triangleCoveringNumberOn G Z ≤ 2 := by
    apply covering_number_on_le_two_of_subset_four G Z _ ((e \ {v}) ∪ (f \ {v}))
    · intro t ht
      simp [Z, trianglesAvoiding, T_ef] at ht
      rcases ht with ⟨⟨h1, _⟩ | ⟨h1, _⟩, _⟩
      · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h1).1
    · -- Card ≤ 4
      have h_disjoint : (e \ {v}) ∩ (f \ {v}) = ∅ := by
        ext x; simp [h_inter]; tauto
      calc ((e \ {v}) ∪ (f \ {v})).card
          = (e \ {v}).card + (f \ {v}).card := Finset.card_union_of_disjoint h_disjoint
        _ = 2 + 2 := by simp [Finset.card_sdiff, he, hf, h_inter]
        _ = 4 := by ring
        _ ≤ 4 := le_refl _
    · -- Z vertices ⊆ (e \ {v}) ∪ (f \ {v})
      intro t ht
      have h_avoid : v ∉ t := by simp [Z, trianglesAvoiding] at ht; exact ht.2
      have h_in_T : t ∈ T_ef := by simp [Z, trianglesAvoiding] at ht; exact ht.1
      sorry -- Need avoiding_v_vertices
  calc triangleCoveringNumberOn G T_ef
      = triangleCoveringNumberOn G (Y_v ∪ Z) := by rw [← h_decomp]
    _ ≤ triangleCoveringNumberOn G Y_v + triangleCoveringNumberOn G Z := tau_union_le_sum G Y_v Z
    _ ≤ 2 + 2 := Nat.add_le_add h_Yv_bound h_Z_bound
    _ = 4 := by ring

-- Main theorem for ν = 4
theorem tuza_nu4_v_decomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  sorry

end
