/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 54d5ceec-33d8-4d9d-b060-be51eceaca22

The following was proved by Aristotle:

- lemma inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
      triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e))

- theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G
-/

/-
Tuza ν ≤ 3: Gap Closer via Maximality Contradiction

KEY INSIGHT (from Gemini analysis):
If τ(T_e) ≥ 3, then T_e contains 3 edge-disjoint triangles.
These 3 triangles could replace {e, m} in packing M, giving larger packing.
This contradicts maximality of M.
Therefore τ(T_e) ≤ 2.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/- Aristotle failed to find a proof. -/
-- KEY LEMMA: τ(T_e) ≥ 3 implies 3 edge-disjoint triangles in T_e
lemma three_disjoint_of_tau_ge_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3)
    (h : triangleCoveringNumberOn G T ≥ 3) :
    ∃ t1 t2 t3 : Finset V, t1 ∈ T ∧ t2 ∈ T ∧ t3 ∈ T ∧
    (t1 ∩ t2).card ≤ 1 ∧ (t1 ∩ t3).card ≤ 1 ∧ (t2 ∩ t3).card ≤ 1 := by
  sorry

/- Aristotle failed to find a proof. -/
-- MAXIMALITY CONTRADICTION: 3 edge-disjoint in T_e would extend packing
lemma tau_T_le_2_of_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M)
    (h_nu_small : M.card ≤ 3) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry

-- INDUCTIVE BOUND (from proven lemmas)
lemma inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
      triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
  unfold triangleCoveringNumberOn;
  -- Let $E_1$ and $E_2$ be minimal edge covers for the triangles in $T_e$ and $S_e$ respectively.
  obtain ⟨E1, hE1⟩ : ∃ E1 : Finset (Sym2 V), E1 ⊆ G.edgeFinset ∧ (∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E1, e ∈ t.sym2) ∧ E1.card = Option.getD (Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2}))) 0 := by
    have h_min_exists : ∃ E1 ∈ Finset.powerset G.edgeFinset, (∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E1, e ∈ t.sym2) ∧ ∀ E2 ∈ Finset.powerset G.edgeFinset, (∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E2, e ∈ t.sym2) → Finset.card E1 ≤ Finset.card E2 := by
      have h_min_exists : ∃ E1 ∈ Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset), ∀ E2 ∈ Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset), Finset.card E1 ≤ Finset.card E2 := by
        apply_rules [ Finset.exists_min_image ];
        refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ trianglesSharingEdge ];
        intro t ht h; rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        exact ⟨ Sym2.mk ( a, b ), by aesop ⟩;
      grind;
    obtain ⟨ E1, hE1₁, hE1₂, hE1₃ ⟩ := h_min_exists;
    have h_min_exists : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2})) = some (Finset.card E1) := by
      refine' le_antisymm _ _;
      · exact Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE1₁, hE1₂ ⟩ ) );
      · simp +zetaDelta at *;
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE1₃ x hx₁ hx₂ );
    exact ⟨ E1, Finset.mem_powerset.mp hE1₁, hE1₂, h_min_exists.symm ▸ rfl ⟩;
  -- Let $E_2$ be a minimal edge cover for the triangles in $S_e$.
  obtain ⟨E2, hE2⟩ : ∃ E2 : Finset (Sym2 V), E2 ⊆ G.edgeFinset ∧ (∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E2, e ∈ t.sym2) ∧ E2.card = Option.getD (Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2}))) 0 := by
    have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2 } ) ).Nonempty from ?_ );
    · rcases this with ⟨ a, ha ⟩ ; rw [ ha ] ; simp +decide [ Option.getD ] ;
      have := Finset.mem_of_min ha; simp_all +decide [ Finset.mem_image ] ;
      exact ⟨ this.choose, this.choose_spec.1.1, this.choose_spec.1.2, this.choose_spec.2 ⟩;
    · simp +zetaDelta at *;
      refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ Finset.subset_iff ];
      intro t ht ht'; have := ht.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      rcases Finset.card_eq_three.mp ht with ⟨ a, b, c, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
  -- The union of $E_1$ and $E_2$ is an edge cover for all triangles in $G$.
  have h_union : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E1 ∪ E2, e ∈ t.sym2 := by
    intro t ht
    by_cases h_te : t ∈ trianglesSharingEdge G e;
    · exact Exists.elim ( hE1.2.1 t h_te ) fun e he => ⟨ e, Finset.mem_union_left _ he.1, he.2 ⟩;
    · exact Exists.elim ( hE2.2.1 t ( Finset.mem_sdiff.mpr ⟨ ht, h_te ⟩ ) ) fun e he => ⟨ e, Finset.mem_union_right _ he.1, he.2 ⟩;
  have h_union_card : (E1 ∪ E2).card ≤ Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2})).min 0 + Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2})).min 0 := by
    exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add hE1.2.2.le hE2.2.2.le );
  refine' le_trans _ h_union_card;
  unfold triangleCoveringNumber;
  have h_min_le_union : ∀ E' ∈ Finset.filter (isTriangleCover G) G.edgeFinset.powerset, (Option.getD (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)).min 0) ≤ E'.card := by
    intro E' hE'
    have h_min_le_union : ∀ E' ∈ Finset.filter (isTriangleCover G) G.edgeFinset.powerset, (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)).min ≤ E'.card := by
      exact fun E' hE' => Finset.min_le ( Finset.mem_image_of_mem _ hE' );
    convert h_min_le_union E' hE' using 1;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> simp +decide [ h ];
    · exact absurd h ( ne_of_lt ( lt_of_le_of_lt ( Finset.min_le ( Finset.mem_image_of_mem _ hE' ) ) ( WithTop.coe_lt_top _ ) ) );
    · rfl;
  apply h_min_le_union;
  simp +decide [ *, isTriangleCover ];
  simp_all +decide [ Finset.subset_iff, Set.subset_def ]

-- MAIN THEOREM
noncomputable section AristotleLemmas

#check Finset.sym2

lemma remainder_empty_of_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    (G.cliqueFinset 3) \ (M.biUnion (trianglesSharingEdge G)) = ∅ := by
      unfold isMaxPacking at hM;
      -- Assume there exists a triangle $t$ in the set difference. Then $t$ does not share an edge with any triangle in $M$.
      by_contra h_nonempty
      obtain ⟨t, ht⟩ : ∃ t ∈ G.cliqueFinset 3, t ∉ M.biUnion (trianglesSharingEdge G) := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty h_nonempty ) fun x hx => ⟨ x, Finset.mem_sdiff.mp hx |>.1, Finset.mem_sdiff.mp hx |>.2 ⟩;
      -- Since $t$ does not share an edge with any triangle in $M$, $M \cup \{t\}$ is a packing.
      have h_packing : isTrianglePacking G (M ∪ {t}) := by
        constructor <;> simp_all +decide [ isTrianglePacking ];
        · simp_all +decide [ Finset.subset_iff, SimpleGraph.IsNClique ];
        · simp_all +decide [ Set.Pairwise ];
          simp_all +decide [ Finset.inter_comm, trianglesSharingEdge ];
          exact ⟨ fun x hx hx' => Nat.le_of_lt_succ ( ht.2 x hx ht.1 ), fun x hx hx' => Nat.le_of_lt_succ ( ht.2 x hx ht.1 ) ⟩;
      -- Since $M \cup \{t\}$ is a packing, its cardinality is at most the triangle packing number.
      have h_card_le : (M ∪ {t}).card ≤ trianglePackingNumber G := by
        unfold trianglePackingNumber;
        have h_card_le : (M ∪ {t}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
          simp +zetaDelta at *;
          exact ⟨ Insert.insert t M, ⟨ Finset.insert_subset_iff.mpr ⟨ by simpa using ht.1, hM.1.1 ⟩, h_packing ⟩, rfl ⟩;
        have := Finset.le_max h_card_le;
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
      rw [ Finset.card_union ] at h_card_le ; simp_all +decide;
      obtain ⟨ x, hx ⟩ := h_card_le; simp_all +decide [ Finset.inter_comm ] ;
      simp_all +decide [ trianglesSharingEdge ];
      have := hM.1.1 hx.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      exact absurd ( ht.2 x hx.1 ht.1.1 ht.1.2 ) ( by rw [ hx.2 ] ; simp +decide [ ht.1.2 ] )

lemma Finset_min_le_min_of_subset {s t : Finset ℕ} (h : s ⊆ t) (hs : s.Nonempty) :
    t.min.getD 0 ≤ s.min.getD 0 := by
      -- Since $s \subseteq t$, every element in $s$ is also in $t$. Therefore, the minimum element in $t$ must be less than or equal to the minimum element in $s$.
      have h_min_le : ∀ x ∈ s, Finset.min t ≤ x := by
        exact fun x hx => Finset.min_le <| h hx;
      -- Apply `h_min_le` to the minimum element of `s`.
      obtain ⟨x, hx⟩ : ∃ x ∈ s, ∀ y ∈ s, x ≤ y := by
        exact ⟨ Finset.min' s hs, Finset.min'_mem s hs, fun y hy => Finset.min'_le _ _ hy ⟩;
      -- Apply `h_min_le` to the minimum element of `s` to conclude the proof.
      have h_min_le_s : Finset.min t ≤ x := by
        exact h_min_le x hx.1;
      rw [ show s.min = ↑x from _ ];
      · cases h : Finset.min t <;> aesop;
      · exact le_antisymm ( Finset.min_le hx.1 ) ( Finset.le_min fun y hy => WithTop.coe_le_coe.mpr ( hx.2 y hy ) )

lemma triangleCoveringNumberOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 : Finset (Finset V)) (h : T1 ⊆ T2) (hT2 : T2 ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G T1 ≤ triangleCoveringNumberOn G T2 := by
      by_contra h_contra;
      apply_rules [ Finset_min_le_min_of_subset ];
      · grind;
      · refine' ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ _, _ ⟩ ) ⟩;
        exact Finset.filter ( fun e => ∃ t ∈ T2, e ∈ t.sym2 ) G.edgeFinset;
        · aesop_cat;
        · intro t ht; have := hT2 ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          rcases this with ⟨ h1, h2 ⟩;
          rcases Finset.card_eq_three.mp h2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop

lemma triangleCoveringNumberOn_union_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 : Finset (Finset V)) (hT1 : T1 ⊆ G.cliqueFinset 3) (hT2 : T2 ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (T1 ∪ T2) ≤ triangleCoveringNumberOn G T1 + triangleCoveringNumberOn G T2 := by
      -- Let $E1$ and $E2$ be two minimum covers for $T1$ and $T2$ respectively.
      obtain ⟨E1, hE1⟩ : ∃ E1, E1 ∈ Finset.powerset G.edgeFinset ∧ (∀ t ∈ T1, ∃ e ∈ E1, e ∈ t.sym2) ∧ E1.card = triangleCoveringNumberOn G T1 := by
        have h_exists_E1 : ∃ E1 ∈ Finset.powerset G.edgeFinset, (∀ t ∈ T1, ∃ e ∈ E1, e ∈ t.sym2) := by
          refine' ⟨ G.edgeFinset, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
          intro t ht; specialize hT1 ht; rcases hT1 with ⟨ ht1, ht2 ⟩ ; rcases Finset.card_eq_three.mp ht2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use s(a, b); aesop;
        have h_min_card : ∃ m ∈ Finset.image Finset.card (Finset.powerset G.edgeFinset |>.filter (fun E' => ∀ t ∈ T1, ∃ e ∈ E', e ∈ t.sym2)), ∀ n ∈ Finset.image Finset.card (Finset.powerset G.edgeFinset |>.filter (fun E' => ∀ t ∈ T1, ∃ e ∈ E', e ∈ t.sym2)), m ≤ n := by
          exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ h_exists_E1.choose_spec.1, h_exists_E1.choose_spec.2 ⟩ ) ⟩, Finset.min'_mem _ _, fun n hn => Finset.min'_le _ _ hn ⟩;
        unfold triangleCoveringNumberOn;
        obtain ⟨ m, hm₁, hm₂ ⟩ := h_min_card;
        rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ T1, ∃ e ∈ E', e ∈ t.sym2 } ) ).min = some m from ?_ ];
        · grind;
        · exact le_antisymm ( Finset.min_le hm₁ ) ( Finset.le_min fun n hn => WithTop.coe_le_coe.mpr ( hm₂ n hn ) );
      obtain ⟨E2, hE2⟩ : ∃ E2, E2 ∈ Finset.powerset G.edgeFinset ∧ (∀ t ∈ T2, ∃ e ∈ E2, e ∈ t.sym2) ∧ E2.card = triangleCoveringNumberOn G T2 := by
        unfold triangleCoveringNumberOn;
        have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ T2, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ) from ?_ );
        · obtain ⟨ a, ha ⟩ := this; rw [ ha ] ; simp +decide [ Option.getD ] ;
          replace ha := Finset.mem_of_min ha; aesop;
        · simp;
          exact ⟨ G.edgeFinset, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.Subset.refl _ ), fun t ht => by
            have := hT2 ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            rcases this with ⟨ h1, h2 ⟩;
            rcases Finset.card_eq_three.mp h2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop ⟩ ⟩;
      refine' le_trans ( Finset_min_le_min_of_subset _ _ ) _;
      exact { ( E1 ∪ E2 ).card };
      · simp_all +decide [ Finset.subset_iff ];
        exact ⟨ E1 ∪ E2, ⟨ fun x hx => by aesop, fun t ht => by rcases ht with ( ht | ht ) <;> [ exact Exists.elim ( hE1.2.1 t ht ) fun e he => ⟨ e, Finset.mem_union_left _ he.1, he.2 ⟩ ; exact Exists.elim ( hE2.2.1 t ht ) fun e he => ⟨ e, Finset.mem_union_right _ he.1, he.2 ⟩ ] ⟩, rfl ⟩;
      · exact ⟨ _, Finset.mem_singleton_self _ ⟩;
      · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add hE1.2.2.le hE2.2.2.le )

lemma triangleCoveringNumberOn_biUnion_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset α) (f : α → Finset (Finset V))
    (hf : ∀ x ∈ S, f x ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (S.biUnion f) ≤ ∑ x ∈ S, triangleCoveringNumberOn G (f x) := by
      induction' S using Finset.induction with x S hxS ih;
      · unfold triangleCoveringNumberOn;
        simp +decide [ Finset.min ];
        rw [ Finset.inf_eq_iInf ];
        rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
        rotate_left;
        exact 0;
        · exact fun _ => zero_le _;
        · exact fun w hw => ⟨ ∅, by simp +decide ; exact hw ⟩;
        · rfl;
      · rw [ Finset.sum_insert hxS, Finset.biUnion_insert ];
        refine' le_trans ( triangleCoveringNumberOn_union_le _ _ _ _ _ ) ( add_le_add_left ( ih fun y hy => hf y ( Finset.mem_insert_of_mem hy ) ) _ );
        · exact hf x ( Finset.mem_insert_self x S );
        · exact Finset.biUnion_subset.2 fun y hy => hf y ( Finset.mem_insert_of_mem hy )

lemma cliques_deleteEdges_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    (G.deleteEdges e.sym2).cliqueFinset 3 = G.cliqueFinset 3 \ trianglesSharingEdge G e := by
      -- A triangle in G.deleteEdges e.sym2 is a set of three vertices where every pair is adjacent in G and none of the edges are in e.sym2.
      ext t; simp [SimpleGraph.deleteEdges];
      unfold trianglesSharingEdge; constructor <;> intro h <;> simp_all +decide [ SimpleGraph.isNClique_iff, Finset.subset_iff ] ;
      · refine' ⟨ _, fun _ => _ ⟩;
        · intro u hu v hv huv; have := h.1 hu hv; aesop;
        · refine' lt_of_not_ge fun h' => _;
          obtain ⟨ v, hv, w, hw, hvw ⟩ := Finset.one_lt_card.1 h';
          have := h.1 ( Finset.mem_coe.2 ( Finset.mem_of_mem_inter_left hv ) ) ( Finset.mem_coe.2 ( Finset.mem_of_mem_inter_left hw ) ) hvw; simp_all +decide [ SimpleGraph.fromEdgeSet ] ;
      · intro x hx y hy; aesop;
        · exact left_1 hx hy a;
        · exact right_1.not_le ( Finset.one_lt_card.2 ⟨ x, by aesop, y, by aesop ⟩ )

lemma cover_remains_cover_of_disjoint_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V)
    (T : Finset (Finset V))
    (hT : ∀ t ∈ T, (t ∩ e).card ≤ 1)
    (E : Finset (Sym2 V))
    (hE_subset : E ⊆ G.edgeFinset)
    (hE : ∀ t ∈ T, ∃ f ∈ E, f ∈ t.sym2) :
    ∀ t ∈ T, ∃ f ∈ E \ e.sym2, f ∈ t.sym2 := by
      intro t ht;
      obtain ⟨ f, hfE, hft ⟩ := hE t ht;
      by_cases hf : f ∈ e.sym2;
      · rcases f with ⟨ u, v ⟩;
        have := hT t ht;
        rw [ Finset.card_le_one_iff ] at this;
        specialize @this u v ; simp_all +decide [ Finset.mem_sym2_iff ];
        exact absurd ( hE_subset hfE ) ( by simp +decide [ SimpleGraph.adj_comm ] );
      · exact ⟨ f, Finset.mem_sdiff.mpr ⟨ hfE, hf ⟩, hft ⟩

lemma tau_on_diff_le_tau_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (G.cliqueFinset 3 \ trianglesSharingEdge G e) ≤
    triangleCoveringNumber (G.deleteEdges e.sym2) := by
      -- By definition of $T$, the triangles of $G \setminus e.sym2$ are exactly $T$.
      have hT_eq : (G.deleteEdges e.sym2).cliqueFinset 3 = G.cliqueFinset 3 \ trianglesSharingEdge G e := by
        exact?;
      refine' Finset_min_le_min_of_subset _ _;
      · simp +decide [ Finset.subset_iff, hT_eq ];
        rintro _ E hE₁ hE₂ rfl;
        refine' ⟨ E, ⟨ _, _ ⟩, rfl ⟩ <;> simp_all +decide [ SimpleGraph.deleteEdges ];
        intro t ht ht'; specialize hE₂; unfold isTriangleCover at hE₂; aesop;
      · simp +decide [ isTriangleCover ];
        refine' ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.Subset.refl _ ), _, _ ⟩ ⟩ <;> simp_all +decide [ isTriangleCover ];
        intro t ht ht'; rw [ Finset.ext_iff ] at hT_eq; specialize hT_eq t; simp_all +decide [ SimpleGraph.IsNClique ] ;
        rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use s(a, b) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;

lemma nu_deleteEdges_le_nu_sub_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    trianglePackingNumber (G.deleteEdges e.sym2) + 1 ≤ trianglePackingNumber G := by
      -- Let $M'$ be a maximum packing of $G'$.
      obtain ⟨M', hM', hM'_card⟩ : ∃ M' : Finset (Finset V), isTrianglePacking (G.deleteEdges e.sym2) M' ∧ M'.card = trianglePackingNumber (G.deleteEdges e.sym2) := by
        have h_max_packing : ∃ M' ∈ (G.deleteEdges e.sym2).cliqueFinset 3 |>.powerset.filter (isTrianglePacking (G.deleteEdges e.sym2)), M'.card = trianglePackingNumber (G.deleteEdges e.sym2) := by
          unfold trianglePackingNumber;
          have := Finset.max_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking ( G.deleteEdges ( e.sym2 : Set ( Sym2 V ) ) ) ) ( ( G.deleteEdges ( e.sym2 : Set ( Sym2 V ) ) ).cliqueFinset 3 |> Finset.powerset ) ) ).Nonempty from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_max ha; aesop;
          · simp +decide [ isTrianglePacking ];
            exact ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide [ isTrianglePacking ] ⟩ ⟩;
        grind;
      -- Then $M' \cup \{e\}$ is a packing in $G$.
      have h_union_packing : isTrianglePacking G (M' ∪ {e}) := by
        refine' ⟨ _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
        · simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
          exact fun x hx => by have := hM'.1 hx; exact this.1.mono ( by simp +decide [ SimpleGraph.deleteEdges ] ) ;
        · intro t1 ht1 t2 ht2 hne; by_cases h : t1 = e <;> by_cases h' : t2 = e <;> simp_all +decide [ Set.Pairwise ] ;
          · have := hM'.1 ht2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            have := this.1; simp_all +decide [ SimpleGraph.isClique_iff, Set.Pairwise ] ;
            contrapose! this;
            obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 this; use x, by aesop, y, by aesop; ; aesop;
          · have := hM'.1 ht1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            have := Finset.card_eq_three.mp this.2; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := this; simp_all +decide [ SimpleGraph.isClique_iff ] ;
            rw [ Finset.card_le_one_iff ] ; aesop;
      -- Since $M' \cup \{e\}$ is a packing in $G$, its size is at most the triangle packing number of $G$.
      have h_union_card : (M' ∪ {e}).card ≤ trianglePackingNumber G := by
        unfold trianglePackingNumber;
        have h_union_card : (M' ∪ {e}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
          refine' Finset.mem_image.mpr ⟨ M' ∪ { e }, _, rfl ⟩;
          simp_all +decide [ isTrianglePacking ];
        have h_max_card : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
          intro x hx;
          have := Finset.le_max hx;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        exact h_max_card _ h_union_card;
      by_cases he' : e ∈ M' <;> simp_all +decide;
      have := hM'.1 he'; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      rcases Finset.card_eq_three.mp he.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; simp_all +decide [ Set.Pairwise ]

lemma nu_eq_zero_imp_tau_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) :
    triangleCoveringNumber G = 0 := by
      -- Since there are no triangles in G, the empty set is a valid triangle cover.
      have h_empty_cover : isTriangleCover G ∅ := by
        constructor <;> simp +decide [ trianglePackingNumber ] at *;
        have h_empty : ∀ t ∈ G.cliqueFinset 3, ¬isTrianglePacking G {t} := by
          intro t ht htp; have := h; simp_all +decide [ Finset.max ] ;
          have h_empty : (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset).sup (WithBot.some ∘ Finset.card) ≥ 1 := by
            exact Finset.le_sup ( f := WithBot.some ∘ Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ( by simpa using ht ) ), htp ⟩ ) |> le_trans ( by simp +decide );
          cases h : ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) |> Finset.sup ) ( WithBot.some ∘ Finset.card ) <;> aesop;
        simp_all +decide [ isTrianglePacking ];
      unfold triangleCoveringNumber;
      simp_all +decide [ Finset.min ];
      rw [ Finset.inf_eq_iInf ];
      rw [ iInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
      rotate_right;
      exact 0;
      · rfl;
      · exact fun _ => zero_le _;
      · exact fun w hw => ⟨ ∅, by aesop ⟩

end AristotleLemmas

theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- Let $M$ be a maximum triangle packing of $G$. Then $|M| = \nu(G)$.
  obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), isMaxPacking G M := by
    unfold isMaxPacking;
    have := Finset.max_of_nonempty ( show ( G.cliqueFinset 3 ).powerset.filter ( isTrianglePacking G ) |>.image Finset.card |>.Nonempty from ?_ );
    · obtain ⟨ a, ha ⟩ := this;
      have := Finset.mem_of_max ha;
      unfold trianglePackingNumber; aesop;
    · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by unfold isTrianglePacking; aesop ⟩ ) ⟩;
  -- Since $M$ is a maximum packing, we have $|M| = \nu(G) \leq 3$.
  have hM_card : M.card = trianglePackingNumber G := by
    exact hM.2;
  -- By `tau_T_le_2_of_max_packing`, $\tau(T_e) \leq 2$.
  have h_tau_T_le_2 : ∀ e ∈ M, triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
    exact fun e he => tau_T_le_2_of_max_packing G M hM e he ( by linarith );
  -- By `inductive_bound`, $\tau(G) \leq \tau(T_e) + \tau(T \setminus T_e)$.
  have h_inductive_bound : triangleCoveringNumber G ≤ ∑ e ∈ M, triangleCoveringNumberOn G (trianglesSharingEdge G e) := by
    have h_inductive_bound : triangleCoveringNumber G ≤ triangleCoveringNumberOn G (M.biUnion (trianglesSharingEdge G)) := by
      -- Since $M$ is a maximum packing, the set of triangles sharing an edge with $M$ is exactly the set of all triangles in $G$.
      have h_trianglesSharingEdge_eq : M.biUnion (trianglesSharingEdge G) = G.cliqueFinset 3 := by
        have := remainder_empty_of_max_packing G M hM;
        simp_all +decide [ Finset.ext_iff ];
        exact fun a => ⟨ fun ⟨ e, he, ha ⟩ => by unfold trianglesSharingEdge at ha; aesop, fun ha => this a ha ⟩;
      rw [h_trianglesSharingEdge_eq];
      refine' Finset_min_le_min_of_subset _ _;
      · simp +decide [ Finset.subset_iff, isTriangleCover ];
      · simp +zetaDelta at *;
        refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ Finset.subset_iff ];
        intro t ht; obtain ⟨ u, v, w, hu, hv, hw, h ⟩ := Finset.card_eq_three.mp ht.2; use s(u, v); simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    refine' le_trans h_inductive_bound _;
    apply triangleCoveringNumberOn_biUnion_le;
    exact fun e he => Finset.filter_subset _ _;
  exact h_inductive_bound.trans ( by simpa [ mul_comm, hM_card ] using Finset.sum_le_sum h_tau_T_le_2 )

end