/-
  Slot 26: Vertex-Saturating Cover Strategy for ν=4

  Key Insight (from Gemini + Codex consultation):
  If a cover C hits all vertices of packing element e, then C automatically
  covers all bridges X(e,·) since bridges must contain the shared vertex.

  This enables τ(T_e) ≤ 2, which by induction gives τ(G) ≤ 2ν.

  SCAFFOLDING: Full proofs from slot24 (uuid 3042f3e3) included below.
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (matching proven lemmas exactly)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglePackingNumber : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def T (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G e)

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

def triangleCoveringNumberOn (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def coverHitsAllVertices (C : Finset (Sym2 V)) (t : Finset V) : Prop :=
  ∀ v ∈ t, ∃ e ∈ C, v ∈ e

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: lemma_2_2 (from slot24, uuid 3042f3e3)
-- ══════════════════════════════════════════════════════════════════════════════

lemma lemma_2_2 (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S G e M → t2 ∈ S G e M → shareEdge t1 t2 := by
  intros t1 t2 ht1 ht2
  apply Classical.byContradiction
  intro h_contra;
  have h_new_packing : isTrianglePacking G (insert t1 (insert t2 (M.erase e))) := by
    unfold S at ht1 ht2;
    simp_all +decide [ isTrianglePacking ];
    unfold trianglesSharingEdge at ht1 ht2; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
    simp_all +decide [ Finset.inter_comm, shareEdge ];
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun a ha ha' => hM.1.1 ha' |> fun h => by simpa using h;
    · exact fun h => Nat.le_of_lt_succ h_contra;
    · exact fun h => Nat.le_of_lt_succ h_contra;
    · have := hM.1.2; aesop;
  have h_card_new_packing : (insert t1 (insert t2 (M.erase e))).card > M.card := by
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.ext_iff ];
    · omega;
    · intro x hx h; have := hM.1; simp_all +decide [ isTrianglePacking ] ;
      simp_all +decide [ S, Finset.mem_filter ];
      simp_all +decide [ trianglesSharingEdge ];
      have := this.2 h he; simp_all +decide [ Finset.inter_comm ] ;
      exact absurd ( this ( by aesop_cat ) ) ( by linarith );
    · constructor;
      · contrapose! h_contra;
        simp_all +decide [ Finset.ext_iff, shareEdge ];
        have h_card_t1 : t1.card = 3 := by
          have h_card_t1 : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht1 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact h_card_t1.card_eq;
        rw [ show t1 ∩ t2 = t1 by ext x; aesop ] ; linarith;
      · simp_all +decide [ S ];
        intro x hx; intro H; have := ht1.2 _ H; simp_all +decide [ Finset.ext_iff ] ;
        have := this x hx; simp_all +decide [ Finset.card_le_one ] ;
        have := Finset.card_le_one.2 ( fun a ha b hb => this a ha b hb ) ; simp_all +decide [ trianglesSharingEdge ] ;
        exact this.not_lt ( by rw [ ht1.1.1.card_eq ] ; decide );
  have h_contradiction : (insert t1 (insert t2 (M.erase e))).card ≤ trianglePackingNumber G := by
    apply Finset.le_max_of_eq;
    apply Finset.mem_image_of_mem;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_iff.mpr fun x hx => h_new_packing.1 hx ), h_new_packing ⟩;
    unfold trianglePackingNumber;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    simp_all +decide [ Finset.max ];
    exact h _ ( h_new_packing.1 ) h_new_packing;
  exact h_card_new_packing.not_le ( h_contradiction.trans ( hM.2.ge ) )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: mem_X_implies_v_in_t (from slot24, uuid 3042f3e3)
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_X_implies_v_in_t
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) (t : Finset V) (ht : t ∈ X G e f) :
    ∃ v ∈ e ∩ f, v ∈ t := by
  unfold X at ht
  simp only [Finset.mem_filter] at ht
  obtain ⟨ht_clique, h_e, h_f⟩ := ht
  have h_card_t : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff] at ht_clique
    exact ht_clique.2
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h_inter
  use v
  constructor
  · exact hv.symm ▸ Finset.mem_singleton_self v
  · by_contra hv_notin
    have h1 : (t ∩ e).card ≤ (e \ {v}).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_inter] at hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hx.2
      · intro hxv; rw [hxv] at hx; exact hv_notin hx.1
    have h2 : (e \ {v}).card ≤ 2 := by
      have he_card : e.card = 3 := by
        simp only [SimpleGraph.mem_cliqueFinset_iff] at he; exact he.2
      have : ({v} : Finset V).card = 1 := Finset.card_singleton v
      have hv_in_e : v ∈ e := by
        have := hv.symm ▸ Finset.mem_singleton_self v
        exact Finset.mem_of_mem_inter_left this
      rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hv_in_e), he_card, this]
      omega
    linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: X_eq_empty_of_disjoint (from slot24, uuid 3042f3e3)
-- ══════════════════════════════════════════════════════════════════════════════

lemma X_eq_empty_of_disjoint (e f : Finset V) (h : e ∩ f = ∅) : X G e f = ∅ := by
  unfold X;
  ext1 t; simp_all +decide [ Finset.ext_iff ] ;
  intro ht ht'; have := Finset.card_le_card ( show t ∩ e ⊆ t from Finset.inter_subset_left ) ; have := Finset.card_le_card ( show t ∩ f ⊆ t from Finset.inter_subset_left ) ; simp_all +decide ;
  have := Finset.card_le_card ( show t ∩ e ∪ t ∩ f ⊆ t from Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ; simp_all +decide ;
  rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx hx' => h x ( Finset.mem_of_mem_inter_right hx ) ( Finset.mem_of_mem_inter_right hx' ) ) ] at this ; linarith [ ht.2 ]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2_of_inter_eq_1 (from slot24, uuid 3042f3e3)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_X_le_2_of_inter_eq_1
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
  unfold triangleCoveringNumberOn;
  have h_cover : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ X G e f, ∃ e ∈ E', e ∈ t.sym2 := by
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e ∩ f ∧ ∀ t ∈ X G e f, v ∈ t := by
      exact Exists.elim ( Finset.card_eq_one.mp h_inter ) fun v hv => ⟨ v, hv.symm ▸ Finset.mem_singleton_self _, fun t ht => mem_X_implies_v_in_t G e f he hf h_inter t ht |> fun ⟨ w, hw₁, hw₂ ⟩ => by aesop ⟩;
    obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ e = {v, u, w} ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w := by
      have h_e : e.card = 3 := by
        exact Finset.mem_filter.mp he |>.2.2;
      rw [ Finset.card_eq_three ] at h_e;
      rcases h_e with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      rcases hv.1.1 with ( rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · exact ⟨ y, by tauto, z, by tauto, rfl, by tauto ⟩;
      · exact ⟨ x, by tauto, z, by tauto, by aesop, by tauto, by tauto, by tauto ⟩;
      · exact ⟨ x, hxz, y, hyz, by aesop, by tauto ⟩;
    refine' ⟨ { s(v, u), s(v, w) }, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
    · simp_all +decide [ Set.insert_subset_iff, SimpleGraph.adj_comm ];
    · exact Finset.card_insert_le _ _;
    · intro t ht;
      have := Finset.mem_filter.mp ht |>.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      contrapose! this; aesop;
  obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_cover;
  have h_min_le_2 : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → (Finset.image Finset.card S).min.getD 0 ≤ E'.card := by
    intros S hE'; exact (by
    have h_min_le_2 : (Finset.image Finset.card S).min.getD 0 ≤ Finset.card E' := by
      have h_min_le_2 : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → (Finset.image Finset.card S).min.getD 0 ≤ Finset.card E' := by
        intros S hE'; exact (by
        have h_min_le_2 : ∀ {S : Finset ℕ}, E'.card ∈ S → (Finset.min S).getD 0 ≤ E'.card := by
          intros S hE'; exact (by
          have h_min_le_2 : ∀ {S : Finset ℕ}, E'.card ∈ S → (Finset.min S).getD 0 ≤ E'.card := by
            intros S hE'
            have h_min_le_2 : (Finset.min S).getD 0 ≤ Finset.min S := by
              cases h : Finset.min S <;> aesop
            exact Nat.cast_le.mp ( h_min_le_2.trans ( Finset.min_le hE' ) );
          exact h_min_le_2 hE');
        exact h_min_le_2 ( Finset.mem_image_of_mem _ hE' ))
      exact h_min_le_2 hE';
    exact h_min_le_2);
  exact le_trans ( h_min_le_2 ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE₁, hE₃ ⟩ ) ) hE₂

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (from slot24, uuid 3042f3e3)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_X_le_2 (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
  by_cases h_inter : (e ∩ f).card ≤ 1;
  · cases h_inter.eq_or_lt <;> simp_all +decide;
    · have := hM.1;
      exact tau_X_le_2_of_inter_eq_1 G e f ( this.1 he ) ( this.1 hf ) ‹_›;
    · rw [ X_eq_empty_of_disjoint G e f ‹_› ];
      unfold triangleCoveringNumberOn;
      simp +decide [ Finset.min ];
      rw [ Finset.inf_eq_iInf ];
      simp +decide [ Option.getD ];
      rw [ show ( ⨅ a : Finset ( Sym2 V ), ⨅ ( _ : ( a : Set ( Sym2 V ) ) ⊆ G.edgeSet ), ( a.card : WithTop ℕ ) ) = 0 from ?_ ] ; simp +decide;
      refine' le_antisymm _ _;
      · refine' le_trans ( ciInf_le _ ∅ ) _ <;> simp +decide;
      · exact zero_le _;
  · have := hM.1;
    exact absurd ( this.2 he hf hef ) ( by aesop )

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET 1: Vertex-saturating cover implies bridge coverage
-- ══════════════════════════════════════════════════════════════════════════════

theorem vertex_cover_implies_bridge_cover
    (e f : Finset V) (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_inter : (e ∩ f).card = 1)
    (C : Finset (Sym2 V)) (hC : C ⊆ G.edgeFinset)
    (hC_hits : coverHitsAllVertices C e) :
    ∀ t ∈ X G e f, ∃ edge ∈ C, edge ∈ t.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET 2: S_e always has vertex-saturating cover of size ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

theorem Se_has_vertex_saturating_cover
    (e : Finset V) (M : Finset (Finset V)) (hM : isMaxPacking G M) (he : e ∈ M) :
    ∃ C : Finset (Sym2 V), C ⊆ G.edgeFinset ∧ C.card ≤ 2 ∧
      (∀ t ∈ S G e M, ∃ edge ∈ C, edge ∈ t.sym2) ∧
      coverHitsAllVertices C e := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET 3: τ(T_e) ≤ 2 (MAIN RESULT)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_Te_le_2
    (e : Finset V) (M : Finset (Finset V)) (hM : isMaxPacking G M) (he : e ∈ M) :
    triangleCoveringNumberOn G (T G e M) ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET 4: Inductive step - τ(G) ≤ 2ν
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_2_times_nu
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 2 * M.card := by
  sorry

end
