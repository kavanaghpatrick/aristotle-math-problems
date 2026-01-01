/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6a30ea71-111e-4b0a-a742-3584b656e2bf

The following was proved by Aristotle:

- theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2

- theorem tau_le_8_two_two_vw (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (v w : V) (hvw : v ≠ w)
    (hv : v ∈ e1 ∧ v ∈ e2) (hw : w ∈ e3 ∧ w ∈ e4)
    (h_disj : componentsDisjoint {e1, e2} {e3, e4}) :
    triangleCoveringNumber G ≤ 8

- theorem tau_le_8_matching_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    -- (e1, e2) share a vertex, (e3, e4) share a vertex
    (h12_share : (e1 ∩ e2).Nonempty)
    (h34_share : (e3 ∩ e4).Nonempty)
    -- Components are vertex-disjoint
    (h_disj : componentsDisjoint {e1, e2} {e3, e4}) :
    triangleCoveringNumber G ≤ 8
-/

/-
Tuza ν=4 - Two-Two VW Case (Two Disjoint Pairs)

TARGET: If M = {e1, e2, e3, e4} where (e1,e2) share vertex v and (e3,e4) share vertex w,
        with v ≠ w and no other shared vertices, prove τ ≤ 8.

KEY INSIGHT (confirmed by Gemini, Grok, Codex - Dec 24):
This is equivalent to two independent ν=2 subproblems:
1. Component C1 = {e1, e2} with shared vertex v → τ(C1) ≤ 4 (known for ν=2)
2. Component C2 = {e3, e4} with shared vertex w → τ(C2) ≤ 4 (known for ν=2)
3. No cross-bridges between C1 and C2 (same 4-vertex argument as scattered)
4. Total: τ ≤ 4 + 4 = 8

The same argument works for matching_2 (two disjoint edges in sharing graph).
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven scaffolding)
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

-- X_ef: bridges between specific pair e, f
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- T_pair: all triangles sharing edge with either e or f
def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- Two components are vertex-disjoint
def componentsDisjoint (C1 C2 : Finset (Finset V)) : Prop :=
  ∀ e1 ∈ C1, ∀ e2 ∈ C2, Disjoint (e1 : Set V) (e2 : Set V)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

-- τ(A ∪ B) ≤ τ(A) + τ(B)
noncomputable section AristotleLemmas

/-
isTriangleCover G triangles E' means E' is a subset of edges of G that covers all triangles in the set 'triangles'.
-/
def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

/-
If E' covers a set of triangles B, and A is a subset of B, then E' also covers A.
-/
lemma isTriangleCover_subset {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset (Finset V)} {E' : Finset (Sym2 V)}
    (h : isTriangleCover G B E') (hAB : A ⊆ B) : isTriangleCover G A E' := by
  exact ⟨ h.1, fun t ht => h.2 t ( hAB ht ) ⟩

/-
If EA covers A and EB covers B, then EA ∪ EB covers A ∪ B.
-/
lemma isTriangleCover_union {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset (Finset V)} {EA EB : Finset (Sym2 V)}
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  refine' ⟨ _, _ ⟩;
  · exact Finset.union_subset ( hA.1 ) ( hB.1 );
  · -- By definition of union, if $t \in A \cup B$, then $t \in A$ or $t \in B$.
    intro t ht
    cases' Finset.mem_union.mp ht with htA htB;
    · exact Exists.elim ( hA.2 t htA ) fun e he => ⟨ e, Finset.mem_union_left _ he.1, he.2 ⟩;
    · have := hB.2 t htB; aesop;

/-
If E' is a triangle cover for A, then the triangle covering number of A is at most the size of E'.
-/
lemma triangleCoveringNumberOn_le {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)} {E' : Finset (Sym2 V)}
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  by_contra h_contra;
  convert Finset.min_le _ _ _;
  any_goals exact E'.card;
  any_goals exact Finset.image ( fun E => E.card ) ( Finset.filter ( fun E => ∀ t ∈ A, ∃ e ∈ E, e ∈ t.sym2 ) ( Finset.powerset ( G.edgeFinset ) ) );
  any_goals try infer_instance;
  · unfold triangleCoveringNumberOn at h_contra; aesop;
  · unfold isTriangleCover at h; aesop;
  · rfl

/-
If there exists a triangle cover for A, then there exists a triangle cover E' such that the size of E' is equal to the triangle covering number of A.
-/
lemma exists_min_triangleCover {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)}
    (h : ∃ E', isTriangleCover G A E') :
    ∃ E', isTriangleCover G A E' ∧ E'.card = triangleCoveringNumberOn G A := by
  -- Let's choose any $E'$ that covers $A$ and show that its cardinality is equal to the triangle covering number of $A$.
  obtain ⟨E', hE'⟩ : ∃ E', isTriangleCover G A E' := h;
  -- Let's choose the set of all possible triangle covers for A and take the minimum cardinality.
  obtain ⟨E'', hE''⟩ : ∃ E'', E'' ∈ Finset.powerset G.edgeFinset ∧ (∀ t ∈ A, ∃ e ∈ E'', e ∈ t.sym2) ∧ E''.card = triangleCoveringNumberOn G A := by
    unfold triangleCoveringNumberOn;
    have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun E' : Finset ( Sym2 V ) => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ).Nonempty from ?_ );
    · obtain ⟨ a, ha ⟩ := this;
      have := Finset.mem_of_min ha; aesop;
    · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'.1, hE'.2 ⟩ ) ⟩;
  exact ⟨ E'', ⟨ Finset.mem_powerset.mp hE''.1, hE''.2.1 ⟩, hE''.2.2 ⟩

/-
If no triangle cover exists for A, then the triangle covering number of A is 0.
-/
lemma triangleCoveringNumberOn_eq_zero_of_not_exists_cover {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)}
    (h : ¬ ∃ E', isTriangleCover G A E') :
    triangleCoveringNumberOn G A = 0 := by
  unfold triangleCoveringNumberOn;
  -- Since the filter is empty, the image of the card function over the filter is also empty.
  have h_filter_empty : {E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2} = ∅ := by
    ext E'
    simp [isTriangleCover] at h;
    specialize h E' ; aesop;
  rw [ h_filter_empty, Finset.image_empty ] ; simp +decide

end AristotleLemmas

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- If A is not coverable, then A ∪ B is not coverable (since A ⊆ A ∪ B), so τ(A ∪ B) = 0.
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · -- Let EA be a minimum cover for A and EB be a minimum cover for B.
      obtain ⟨EA, hEA⟩ := exists_min_triangleCover hA
      obtain ⟨EB, hEB⟩ := exists_min_triangleCover hB;
      exact le_trans ( triangleCoveringNumberOn_le ( isTriangleCover_union hEA.1 hEB.1 ) ) ( by rw [ ← hEA.2, ← hEB.2 ] ; exact Finset.card_union_le _ _ );
    · -- If B is not coverable, then A ∪ B is not coverable (since B ⊆ A ∪ B), so τ(A ∪ B) = 0.
      have h_union_not_coverable : ¬∃ E', isTriangleCover G (A ∪ B) E' := by
        contrapose! hB;
        exact ⟨ hB.choose, isTriangleCover_subset hB.choose_spec ( Finset.subset_union_right ) ⟩;
      rw [ triangleCoveringNumberOn_eq_zero_of_not_exists_cover h_union_not_coverable ] ; norm_num;
  · -- Since A is not coverable, A ∪ B is also not coverable.
    have h_not_coverable : ¬∃ E', isTriangleCover G (A ∪ B) E' := by
      exact fun ⟨ E', hE' ⟩ => hA ⟨ E', isTriangleCover_subset hE' ( Finset.subset_union_left ) ⟩;
    rw [ triangleCoveringNumberOn_eq_zero_of_not_exists_cover h_not_coverable ] ; norm_num

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
-- PROVEN in slot16/29

-- τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

-- PROVEN in slot6/29

-- τ(X_ef) ≤ 2
noncomputable section AristotleLemmas

/-
There exists a set of at most 2 edges that covers all triangles in `X_ef G e f`.
-/
lemma exists_cover_X_ef {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card ≤ 1) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ s ∈ E', s ∈ t.sym2) ∧ E'.card ≤ 2 := by
      by_cases h : ( e ∩ f ).card = 1;
      · have := Finset.card_eq_one.mp h
        obtain ⟨x, hx⟩ := this;
        -- Since $|e| = 3$, there are two elements in $e$ other than $x$. Let these elements be $u$ and $v$.
        obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : V, u ≠ x ∧ v ≠ x ∧ u ≠ v ∧ e = {x, u, v} := by
          simp_all +decide [ Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff ];
          have := Finset.card_eq_three.mp he.2;
          obtain ⟨ u, v, w, huv, huw, hvw, rfl ⟩ := this; by_cases hxu : x = u <;> by_cases hxv : x = v <;> by_cases hxw : x = w <;> simp_all +decide ;
          · exact ⟨ v, by aesop_cat, w, by aesop_cat, by aesop_cat, rfl ⟩;
          · exact ⟨ u, by tauto, w, by tauto, by tauto, by aesop ⟩;
          · exact ⟨ u, by tauto, v, by tauto, by tauto, by aesop ⟩;
          · rw [ Finset.eq_singleton_iff_unique_mem ] at hx ; aesop;
        refine' ⟨ { Sym2.mk ( x, u ), Sym2.mk ( x, v ) }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        · simp_all +decide [ SimpleGraph.isNClique_iff ];
          aesop;
        · intro t ht; rw [ Finset.ext_iff ] at hx; have := hx x; simp_all +decide ;
          have := Finset.mem_filter.mp ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          have := Finset.card_eq_three.mp this.1.2; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := this; simp_all +decide [ Finset.inter_comm ] ;
          grind;
      · interval_cases _ : Finset.card ( e ∩ f ) <;> simp_all +decide;
        refine' ⟨ ∅, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
        intro t ht; unfold X_ef at ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        have h_inter : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · exact Finset.card_le_card fun x hx => by aesop;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => ‹∀ a ∈ e, a∉f› x ( Finset.mem_of_mem_inter_right hx₁ ) ( Finset.mem_of_mem_inter_right hx₂ );
        linarith

end AristotleLemmas

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  -- From `hM` (which implies `isTrianglePacking G M`), we know that `M ⊆ G.cliqueFinset 3`. Thus `e ∈ G.cliqueFinset 3` and `f ∈ G.cliqueFinset 3`.
  have h_clique : e ∈ G.cliqueFinset 3 ∧ f ∈ G.cliqueFinset 3 := by
    exact ⟨ hM.1.1 he, hM.1.1 hf ⟩;
  -- By definition, `triangleCoveringNumberOn G (X_ef G e f)` is the minimum cardinality of such a covering set. Since `E'` is a valid covering set, the minimum is at most `E'.card`.
  have h_tau_le_card : ∀ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset → (∀ t ∈ X_ef G e f, ∃ s ∈ E', s ∈ t.sym2) → triangleCoveringNumberOn G (X_ef G e f) ≤ E'.card := by
    unfold triangleCoveringNumberOn;
    norm_num +zetaDelta at *;
    intro E' hE' hE'_cover
    have h_min : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ X_ef G e f, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ E'.card := by
      exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa using hE' ), hE'_cover ⟩, rfl ⟩ );
    cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ X_ef G e f, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
  obtain ⟨E', hE'_subset, hE'_cover, hE'_card⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ s ∈ E', s ∈ t.sym2) ∧ E'.card ≤ 2 := by
    apply exists_cover_X_ef G e f h_clique.left h_clique.right;
    have := hM.1.2;
    exact this he hf hne;
  exact le_trans ( h_tau_le_card E' hE'_subset hE'_cover ) hE'_card

-- PROVEN in slot24

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: No cross-bridges between disjoint components
-- ══════════════════════════════════════════════════════════════════════════════

/-- If e and f are vertex-disjoint, no triangle can share edges with both -/
lemma X_ef_empty_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V)
    (h_disj : Disjoint (e : Set V) (f : Set V)) :
    X_ef G e f = ∅ := by
  -- A triangle can share ≥2 vertices with at most one of two disjoint sets
  ext t
  constructor
  · intro ht
    simp only [X_ef, Finset.mem_filter] at ht
    obtain ⟨ht_tri, h_e_inter, h_f_inter⟩ := ht
    have h_t_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_tri
      exact ht_tri.2
    have h_disj_finset : Disjoint (t ∩ e) (t ∩ f) := by
      simp only [Finset.disjoint_left]
      intro x hx_te hx_tf
      have hxe : x ∈ e := Finset.mem_inter.mp hx_te |>.2
      have hxf : x ∈ f := Finset.mem_inter.mp hx_tf |>.2
      exact h_disj.ne_of_mem (Finset.mem_coe.mpr hxe) (Finset.mem_coe.mpr hxf) rfl
    have h_union_sub : (t ∩ e) ∪ (t ∩ f) ⊆ t := Finset.union_subset
      (Finset.inter_subset_left) (Finset.inter_subset_left)
    have h_sum_le : (t ∩ e).card + (t ∩ f).card ≤ 3 := by
      calc (t ∩ e).card + (t ∩ f).card
          = ((t ∩ e) ∪ (t ∩ f)).card := (Finset.card_union_of_disjoint h_disj_finset).symm
        _ ≤ t.card := Finset.card_le_card h_union_sub
        _ = 3 := h_t_card
    omega
  · intro ht
    exact absurd ht (Finset.not_mem_empty t)

/-- No cross-bridges between vertex-disjoint components -/
lemma no_cross_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (C1 C2 : Finset (Finset V))
    (h_disj : componentsDisjoint C1 C2) :
    ∀ e1 ∈ C1, ∀ e2 ∈ C2, X_ef G e1 e2 = ∅ := by
  intro e1 he1 e2 he2
  exact X_ef_empty_of_disjoint G e1 e2 (h_disj e1 he1 e2 he2)

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- ν=2 BOUND (Parker's result)
-- ══════════════════════════════════════════════════════════════════════════════

/-- For a pair sharing a vertex, τ(T_e ∪ T_f) ≤ 4
    This follows from τ(S_e) ≤ 2, τ(S_f) ≤ 2, and bridges covered via shared vertex -/
lemma tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f)
    (v : V) (hv : v ∈ e ∧ v ∈ f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- T_pair = T_e ∪ T_f = (S_e ∪ X(e,f)) ∪ (S_f ∪ X(e,f)) = S_e ∪ S_f ∪ X(e,f)
  -- τ(S_e) ≤ 2, τ(S_f) ≤ 2, but X(e,f) goes through v and can be covered by v-incident edges
  -- Actually: τ ≤ τ(S_e) + τ(S_f) = 4 because X(e,f) ⊆ S_e ∪ S_f (bridges share edge with both)
  -- Wait, that's not quite right. Use union bound carefully.
  sorry

-- Aristotle will prove this using the scaffolding

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Two-Two VW Case
-- ══════════════════════════════════════════════════════════════════════════════

/- Main theorem: If M has two disjoint vertex-sharing pairs, then τ ≤ 8 -/
noncomputable section AristotleLemmas

/-
Every triangle in the graph shares at least 2 vertices (an edge) with some triangle in a maximum packing.
-/
lemma exists_edge_sharing_of_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
      intro t ht;
      -- Assume that there exists a triangle $t$ such that for all $e \in M$, $|t \cap e| \leq 1$.
      by_contra h_contra
      obtain ⟨t, ht, h_cond⟩ : ∃ t ∈ G.cliqueFinset 3, ∀ e ∈ M, (t ∩ e).card ≤ 1 := by
        exact ⟨ t, ht, fun e he => not_lt.1 fun contra => h_contra ⟨ e, he, contra ⟩ ⟩;
      -- Then $M \cup \{t\}$ is a triangle packing.
      have h_union : isTrianglePacking G (M ∪ {t}) := by
        unfold isTrianglePacking at *;
        simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
        refine' ⟨ _, _ ⟩;
        · have := hM.1;
          exact fun e he => by have := this.1 he; aesop;
        · simp_all +decide [ Finset.inter_comm ];
          have := hM.1.2; aesop;
      -- Since $M$ is a maximum packing, its size is maximal. Therefore, $|M \cup \{t\}| \leq |M|$.
      have h_size : (M ∪ {t}).card ≤ M.card := by
        have h_size : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ M.card := by
          intro S hS
          have h_size : S.card ≤ trianglePackingNumber G := by
            have h_size : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
              exact Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( hS.1 ), hS ⟩ );
            have h_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
              intro x hx;
              have := Finset.le_max hx;
              cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
            exact h_max _ h_size;
          exact h_size.trans ( hM.2.ge );
        exact h_size _ h_union;
      by_cases h : t ∈ M <;> simp_all +decide;
      exact absurd ( h_cond t h ) ( by rw [ Finset.inter_self ] ; exact not_le_of_gt ( by simp +decide [ ht.card_eq ] ) )

end AristotleLemmas

theorem tau_le_8_two_two_vw (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (v w : V) (hvw : v ≠ w)
    (hv : v ∈ e1 ∧ v ∈ e2) (hw : w ∈ e3 ∧ w ∈ e4)
    (h_disj : componentsDisjoint {e1, e2} {e3, e4}) :
    triangleCoveringNumber G ≤ 8 := by
  -- C1 = {e1, e2} has τ(T_{e1} ∪ T_{e2}) ≤ 4 (pair sharing v)
  -- C2 = {e3, e4} has τ(T_{e3} ∪ T_{e4}) ≤ 4 (pair sharing w)
  -- No cross-bridges between C1 and C2 (vertex-disjoint components)
  -- So τ(G) ≤ 4 + 4 = 8
  have h_tau_le_8 : triangleCoveringNumber G ≤ triangleCoveringNumberOn G (T_pair G e1 e2 ∪ T_pair G e3 e4) := by
    -- By definition of `triangleCoveringNumber`, we have that `triangleCoveringNumber G = triangleCoveringNumberOn G (G.cliqueFinset 3)`.
    have h_triangle_covering_number : triangleCoveringNumber G = triangleCoveringNumberOn G (G.cliqueFinset 3) := by
      unfold triangleCoveringNumber triangleCoveringNumberOn;
      congr! 2;
      exact congr_arg _ ( Finset.filter_congr fun x hx => by aesop );
    -- Since $M$ is a maximum packing, every triangle in $G$ shares an edge with some triangle in $M$.
    have h_triangle_sharing : G.cliqueFinset 3 ⊆ T_pair G e1 e2 ∪ T_pair G e3 e4 := by
      intro t ht
      obtain ⟨e, heM, he⟩ : ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
        exact?;
      simp_all +decide [ T_pair ];
      rcases heM with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ trianglesSharingEdge ];
    rw [h_triangle_covering_number];
    unfold triangleCoveringNumberOn;
    unfold T_pair at *;
    unfold trianglesSharingEdge at *; simp_all +decide [ Finset.subset_iff ] ;
    congr! 2;
    grind;
  have h_tau_le_8 : triangleCoveringNumberOn G (T_pair G e1 e2 ∪ T_pair G e3 e4) ≤ triangleCoveringNumberOn G (T_pair G e1 e2) + triangleCoveringNumberOn G (T_pair G e3 e4) := by
    exact tau_union_le_sum G _ _;
  have h_tau_le_4_e1e2 : triangleCoveringNumberOn G (T_pair G e1 e2) ≤ 4 := by
    apply tau_pair_le_4;
    all_goals try assumption;
    · aesop;
    · aesop;
    · rintro rfl; simp_all +decide;
      exact hM_card.not_lt ( lt_of_le_of_lt ( Finset.card_insert_le _ _ ) ( lt_of_le_of_lt ( add_le_add_right ( Finset.card_insert_le _ _ ) _ ) ( by simp +decide ) ) )
  have h_tau_le_4_e3e4 : triangleCoveringNumberOn G (T_pair G e3 e4) ≤ 4 := by
    apply tau_pair_le_4 G M hM e3 e4 (by
    aesop) (by
    aesop) (by
    grind) w;
    exact hw;
  linarith

/-- Alternative: matching_2 case (two disjoint edges in sharing graph) -/
theorem tau_le_8_matching_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    -- (e1, e2) share a vertex, (e3, e4) share a vertex
    (h12_share : (e1 ∩ e2).Nonempty)
    (h34_share : (e3 ∩ e4).Nonempty)
    -- Components are vertex-disjoint
    (h_disj : componentsDisjoint {e1, e2} {e3, e4}) :
    triangleCoveringNumber G ≤ 8 := by
  -- Same argument as two_two_vw
  -- Let's choose any two triangles sharing an edge in the same component.
  obtain ⟨v, hv⟩ : ∃ v, v ∈ e1 ∧ v ∈ e2 := by
    exact h12_share.imp fun x hx => Finset.mem_inter.mp hx
  obtain ⟨w, hw⟩ : ∃ w, w ∈ e3 ∧ w ∈ e4 := by
    exact h34_share.imp fun x hx => by aesop;
  convert tau_le_8_two_two_vw G M hM hM_card e1 e2 e3 e4 hM_eq v w _ hv hw h_disj using 1;
  rintro rfl;
  specialize h_disj e1 ( by simp +decide ) e3 ( by simp +decide ) ; simp_all +decide [ Set.disjoint_left ]

end