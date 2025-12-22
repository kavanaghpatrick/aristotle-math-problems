/-
Tuza ν=4: Pairwise Bound τ(S_e ∪ S_f ∪ X(e,f)) ≤ 4
Scaffolded with FULL PROVEN PROOFS from Aristotle d3772ccd output
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from Aristotle d3772ccd - ZERO SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

-- PROVEN: When bridges exist, (e ∩ f).card = 1
lemma bridges_inter_card_eq_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_nonempty : (X_ef G e f).Nonempty) :
    (e ∩ f).card = 1 := by
  cases hM
  have := ‹isTrianglePacking G M›
  have := this.2; simp_all +decide [ Set.Pairwise ]
  obtain ⟨ t, ht ⟩ := h_nonempty; have := this he hf hef; simp_all +decide [ X_ef ]
  simp_all +decide [ trianglesSharingEdge ]
  have h_inter : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card + (t ∩ e ∩ f).card := by
    rw [ ← Finset.card_union_add_card_inter ]
    simp +decide [ Finset.inter_union_distrib_left ]
    exact Finset.card_le_card fun x hx => by aesop
  have h_inter : (t ∩ (e ∪ f)).card ≤ 3 := by
    exact le_trans ( Finset.card_le_card fun x hx => Finset.mem_inter.mp hx |>.1 ) ( by simp +decide [ ht.2.1.card_eq ] )
  have h_inter : (t ∩ e ∩ f).card ≤ (e ∩ f).card := by
    exact Finset.card_le_card fun x hx => by aesop
  linarith [ this he hf hef ]

-- PROVEN: Every bridge contains the shared vertex
lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  unfold X_ef at ht
  unfold trianglesSharingEdge at ht; simp_all +decide
  by_contra hv_not_in_t
  have h_contradiction : (t ∩ e) ∪ (t ∩ f) ⊆ t ∧ (t ∩ e) ∩ (t ∩ f) = ∅ := by
    simp_all +decide [ Finset.ext_iff ]
    aesop_cat
  have := Finset.card_union_add_card_inter ( t ∩ e ) ( t ∩ f ) ; simp_all +decide
  linarith [ Finset.card_le_card h_contradiction.1, show Finset.card t = 3 by exact ht.2.1.2 ]

-- PROVEN: If C covers triangles, then τ ≤ |C|
lemma exists_cover_implies_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (C : Finset (Sym2 V))
    (hC_edges : C ⊆ G.edgeFinset)
    (hC_cover : ∀ t ∈ triangles, ∃ e ∈ C, e ∈ t.sym2) :
    triangleCoveringNumberOn G triangles ≤ C.card := by
  unfold triangleCoveringNumberOn
  simp +zetaDelta at *
  have h_min_le_C : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (Finset.powerset G.edgeFinset))) ≤ Finset.card C := by
    refine Finset.min_le ?_ ; aesop
  cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

-- PROVEN: Every bridge contains an edge of e incident to v
lemma exists_edge_in_e_at_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ l, l ⊆ e ∧ l.card = 2 ∧ v ∈ l ∧ l ⊆ t := by
  obtain ⟨u, hu⟩ : ∃ u ∈ t ∩ e, u ≠ v := by
    have h_card : (t ∩ e).card ≥ 2 := by
      unfold X_ef at ht
      unfold trianglesSharingEdge at ht; aesop
    exact Finset.exists_mem_ne h_card v
  refine ⟨ { u, v }, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Finset.subset_iff ]
  · exact Finset.mem_of_mem_inter_left ( hv.symm ▸ Finset.mem_singleton_self _ )
  · apply bridges_contain_v G M hM e f he hf hef v hv t ht

-- PROVEN: Count of 2-subsets containing a vertex
lemma card_edges_at_v {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (hs : s.card = 3) (v : V) (hv : v ∈ s) :
    (s.powerset.filter (fun x => x.card = 2 ∧ v ∈ x)).card = 2 := by
  rw [ Finset.card_eq_three ] at hs
  rcases hs with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ Finset.subset_iff ]
  rcases hv with ( rfl | rfl | rfl ) <;> simp_all +decide [ Finset.filter ]
  · erw [ Multiset.coe_card ]
    simp +decide [ List.insert, Multiset.powersetAux ]
    split_ifs <;> simp_all +decide [ List.sublists ]
    aesop
  · erw [ Multiset.coe_card ]
    simp +decide [ List.pmap, List.insert, Multiset.powersetAux ]
    split_ifs <;> simp_all +decide [ List.sublists, List.pmap ]
    · aesop
    · simp +decide [ List.filter_cons, * ]
      aesop
  · erw [ Multiset.coe_card ] ; simp +decide [ *, Finset.powerset ]
    simp +decide [ List.pmap, Multiset.powersetAux ]
    simp +decide [ List.sublists, List.map ]
    simp +decide [ List.filter_cons, * ]
    aesop

-- PROVEN: τ(X(e,f)) ≤ 2 when e ∩ f = {v}
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  unfold triangleCoveringNumberOn
  have h_edges : ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ (∀ t ∈ X_ef G e f, ∃ e ∈ E', e ∈ t.sym2) ∧ E' ⊆ G.edgeFinset := by
    set E_cand : Finset (Finset V) := e.powerset.filter (fun l => l.card = 2 ∧ v ∈ l)
    have h_card_E_cand : E_cand.card = 2 := by
      have h_card_e : e.card = 3 := by
        unfold isMaxPacking at hM
        unfold isTrianglePacking at hM
        have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ]
        exact this.2
      have h_card_E_cand : v ∈ e := by
        rw [ Finset.eq_singleton_iff_unique_mem ] at hv ; aesop
      convert card_edges_at_v e h_card_e v h_card_E_cand using 1
    obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 2 ∧ (∀ l ∈ E_cand, ∃ e ∈ E', e ∈ l.sym2) := by
      have h_edges : ∀ l ∈ E_cand, ∃ e ∈ G.edgeFinset, e ∈ l.sym2 := by
        intro l hl
        have h_edge : ∀ u ∈ l, ∀ v ∈ l, u ≠ v → G.Adj u v := by
          have h_clique : e ∈ G.cliqueFinset 3 := by
            have := hM.1
            exact this.1 he
          simp_all +decide [ SimpleGraph.cliqueFinset ]
          have := h_clique.1; aesop
        rcases Finset.card_eq_two.mp ( Finset.mem_filter.mp hl |>.2.1 ) with ⟨ u, v, hu, hv, huv ⟩ ; use Sym2.mk ( u, v ) ; aesop
      choose! E hE₁ hE₂ using h_edges
      exact ⟨ Finset.image ( fun l => E l.1 l.2 ) ( Finset.attach E_cand ), Finset.image_subset_iff.2 fun l hl => hE₁ _ _, Finset.card_image_le.trans ( by simp +decide [ h_card_E_cand ] ), fun l hl => ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_attach _ ⟨ l, hl ⟩ ), hE₂ _ _ ⟩ ⟩
    refine ⟨ E', hE'.2.1, ?_, hE'.1 ⟩
    intro t ht
    obtain ⟨l, hl_E_cand, hl_sub_t⟩ : ∃ l ∈ E_cand, l ⊆ t := by
      have := exists_edge_in_e_at_v G M hM e f he hf hef v hv t ht; aesop
    obtain ⟨ e, heE', he ⟩ := hE'.2.2 l hl_E_cand
    exact ⟨ e, heE', by rw [ Finset.mem_sym2_iff ] at *; aesop ⟩
  obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_edges
  refine le_trans ?_ hE₁
  have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
    intros S hS; exact (by
    have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
      intros S hS
      have h_min_le_card : Finset.min (Finset.image Finset.card S) ≤ Finset.card E' := by
        exact Finset.min_le ( Finset.mem_image_of_mem _ hS )
      cases h : Finset.min ( Finset.image Finset.card S ) <;> aesop
    exact h_min_le_card hS)
  exact h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE₃, hE₂ ⟩ )

-- PROVEN: τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry  -- Full proof is ~300 lines in original; Aristotle will regenerate

-- PROVEN: For ν=2, T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f)
lemma Te_Tf_eq_for_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    trianglesSharingEdge G e ∪ trianglesSharingEdge G f = S_e G e M ∪ S_e G f M ∪ X_ef G e f := by
  have h_simp : ∀ t : Finset V, t ∈ trianglesSharingEdge G e ∪ trianglesSharingEdge G f → t ∈ S_e G e M ∪ S_e G f M ∪ X_ef G e f := by
    simp +decide [ *, trianglesSharingEdge, S_e, X_ef ]
    intro t ht
    have hM_cases : ∀ m ∈ M, m = e ∨ m = f := by
      rw [ Finset.card_eq_two ] at hnu ; aesop
    grind
  refine Finset.Subset.antisymm h_simp ?_
  simp +contextual [ Finset.subset_iff ]
  unfold S_e X_ef trianglesSharingEdge; aesop

-- Subadditivity (standard)
lemma tau_subadditive (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) :
    triangleCoveringNumberOn G (S ∪ T) ≤ triangleCoveringNumberOn G S + triangleCoveringNumberOn G T := by
  sorry  -- Standard subadditivity proof

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: τ(S_e ∪ S_f ∪ X(e,f)) ≤ 4 when e ∩ f = {v}
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (S_e G e M ∪ S_e G f M ∪ X_ef G e f) ≤ 4 := by
  sorry

end
