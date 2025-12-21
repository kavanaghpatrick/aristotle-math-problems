/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9321e4ee-66b5-4c86-9939-8fdd9a41c93c

The following was proved by Aristotle:

- lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, isMaxPacking G M

- lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S_e G e M → t2 ∈ S_e G e M → shareEdge t1 t2

- lemma lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = trianglePackingNumber G - 1

- lemma inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
      triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e))

- lemma intersecting_family_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_nonempty : S.Nonempty) (hS : S ⊆ G.cliqueFinset 3)
    (h_pair : Set.Pairwise (S : Set (Finset V)) shareEdge) :
    isStar S ∨ isK4 S

- lemma tau_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h_star : isStar S) :
    triangleCoveringNumberOn G S ≤ 1

- lemma covering_number_le_two_of_subset_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (s : Finset V) (hs_card : s.card = 4) (hs_contains : ∀ t ∈ S, t ⊆ s) :
    triangleCoveringNumberOn G S ≤ 2

- lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2

- lemma tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0
-/

/-
Tuza's Conjecture for ν ≤ 3: Assembly of Proven Lemmas
All helper lemmas are PROVEN in prior Aristotle runs.
Goal: Complete the final theorem.
-/

import Mathlib


set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical Pointwise

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

def isStar (S : Finset (Finset V)) : Prop :=
  ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t

def isK4 (S : Finset (Finset V)) : Prop :=
  ∃ s : Finset V, s.card = 4 ∧ ∀ t ∈ S, t ⊆ s

def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglePackingNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  triangles.powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, isMaxPacking G M := by
  -- Since the set of triangle packings is finite, there must be a maximum element.
  have h_max_exists : ∃ M ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G), ∀ M' ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G), M'.card ≤ M.card := by
    apply_rules [ Finset.exists_max_image ];
    -- The empty set is a triangle packing, so the set is nonempty.
    use ∅; simp [isTrianglePacking];
  obtain ⟨ M, hM₁, hM₂ ⟩ := h_max_exists;
  refine' ⟨ M, Finset.mem_filter.mp hM₁ |>.2, _ ⟩;
  refine' le_antisymm _ _;
  · unfold trianglePackingNumber;
    have h_max_card : M.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      exact Finset.mem_image_of_mem _ hM₁;
    have := Finset.le_max h_max_card; aesop;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  · simp +zetaDelta at *;
    unfold trianglePackingNumber;
    unfold Option.getD; aesop;
    have := Finset.mem_of_max heq; aesop;

noncomputable section AristotleLemmas

/-
Any triangle in `S_e(e)` is not in `M \ {e}`.
-/
lemma lemma_2_2_aux_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (e : Finset V) (he : e ∈ M)
    (t : Finset V) (ht : t ∈ S_e G e M) : t ∉ M.erase e := by
      unfold S_e at ht; unfold isTrianglePacking at hM; aesop;
      exact absurd ( right ( by aesop ) ( by aesop ) a ) ( by have := right_1 _ a_1 a; linarith [ Finset.mem_filter.mp left_1 ] )

end AristotleLemmas

lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S_e G e M → t2 ∈ S_e G e M → shareEdge t1 t2 := by
  -- Assume that t1 and t2 do not share an edge. Then, we can replace e with t1 and t2 in M to form a larger packing.
  intros t1 t2 ht1 ht2
  by_contra h_no_edge
  have h_replace : ∃ M', isTrianglePacking G M' ∧ M'.card > M.card := by
    refine' ⟨ M.erase e ∪ { t1, t2 }, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, isTrianglePacking ];
    · unfold S_e at ht1 ht2; aesop;
      · unfold trianglesSharingEdge at *; aesop;
      · unfold trianglesSharingEdge at left_1; aesop;
      · exact Finset.mem_filter.mp ( hM.1.1 a_2 ) |>.2;
      · simp_all +decide [ Set.Pairwise, Finset.mem_insert, Finset.mem_sdiff ];
        simp_all +decide [ Finset.inter_comm, shareEdge ];
        exact ⟨ fun _ => Nat.le_of_lt_succ h_no_edge, fun _ => Nat.le_of_lt_succ h_no_edge, fun a ha ha' b hb hb' hab => hM.1.2 ha hb ( by aesop ) ⟩;
    · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ shareEdge ];
      · omega;
      · intro hne h2; have := lemma_2_2_aux_disjoint G M hM.1 e he t2 ht2; aesop;
      · constructor <;> intro h <;> simp_all +decide [ S_e ];
        · unfold trianglesSharingEdge at ht1 ; aesop;
          exact right_1.not_lt ( lt_of_le_of_lt ( Finset.card_le_card ( Finset.inter_subset_left ) ) h_no_edge );
        · intro H; have := ht1.2 _ H h; simp_all +decide [ trianglesSharingEdge ] ;
          exact this.not_lt ( by rw [ ht1.1.1.card_eq ] ; decide );
  obtain ⟨ M', hM', hM'' ⟩ := h_replace;
  have := hM.2;
  unfold trianglePackingNumber at this;
  have := Finset.le_max ( Finset.mem_image_of_mem Finset.card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( show M' ⊆ G.cliqueFinset 3 from ?_ ), hM' ⟩ ) );
  · cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact hM''.not_le ( by simpa [ Option.getD ] using this );
  · exact hM'.1

lemma lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = trianglePackingNumber G - 1 := by
  -- Since $e$ is part of a maximal packing $M$, removing $e$ from $M$ results in a packing of size $M.card - 1$.
  have h_packing_minus_e : ∃ M' : Finset (Finset V), isTrianglePacking G M' ∧ M'.card = M.card - 1 ∧ M' ⊆ G.cliqueFinset 3 \ trianglesSharingEdge G e := by
    -- Let $M' = M \setminus \{e\}$.
    use M \ {e};
    unfold isMaxPacking at hM; aesop;
    · exact ⟨ Finset.sdiff_subset.trans left.1, fun x hx y hy hxy => left.2 ( Finset.mem_sdiff.mp hx |>.1 ) ( Finset.mem_sdiff.mp hy |>.1 ) hxy ⟩;
    · rw [ ← right, Finset.card_sdiff ] ; aesop;
    · intro t ht; unfold trianglesSharingEdge; aesop;
      · have := left.1 left_1; aesop;
      · have := left.2;
        exact Nat.lt_succ_of_le ( this left_1 he right_1 );
  -- Since $M'$ is a packing of size $M.card - 1$ in the remaining triangles, and $M$ is maximal, this should be the maximum possible. Therefore, the trianglePackingNumberOn of the remaining triangles is exactly $M.card - 1$.
  obtain ⟨M', hM', hM'_card, hM'_subset⟩ := h_packing_minus_e;
  have h_max : ∀ M'' : Finset (Finset V), isTrianglePacking G M'' → M'' ⊆ G.cliqueFinset 3 \ trianglesSharingEdge G e → M''.card ≤ M.card - 1 := by
    intros M'' hM'' hM''_subset
    have h_union : M'' ∪ {e} ⊆ G.cliqueFinset 3 ∧ isTrianglePacking G (M'' ∪ {e}) := by
      unfold isTrianglePacking at *; aesop;
      · have := hM.1.1 he; aesop;
        exact Finset.insert_subset_iff.mpr ⟨ by aesop, left_1 ⟩;
      · simp_all +decide [ Set.Pairwise, Finset.subset_iff ];
        simp_all +decide [ Finset.inter_comm, trianglesSharingEdge ];
        exact ⟨ fun x hx hx' => Nat.le_of_lt_succ ( hM''_subset hx |>.2 ( hM''_subset hx |>.1 ) ), fun x hx hx' => Nat.le_of_lt_succ ( hM''_subset hx |>.2 ( hM''_subset hx |>.1 ) ) ⟩;
    have h_union_card : (M'' ∪ {e}).card ≤ M.card := by
      have h_union_card : (M'' ∪ {e}).card ≤ trianglePackingNumber G := by
        unfold trianglePackingNumber; aesop;
        have h_union_card : (Insert.insert e M'').card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
          exact Finset.mem_image.mpr ⟨ Insert.insert e M'', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr left, right ⟩, rfl ⟩;
        have := Finset.le_max h_union_card; aesop;
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
      exact h_union_card.trans ( hM.2.ge );
    by_cases heM'' : e ∈ M'' <;> simp_all +decide [ Finset.union_eq_left.mpr ];
    · have := hM''_subset heM''; simp_all +decide [ trianglesSharingEdge ] ;
      exact absurd ( this.2 this.1 ) ( by have := this.1.2; aesop );
    · exact Nat.le_sub_one_of_lt h_union_card;
  refine' le_antisymm _ _ <;> simp_all +decide [ trianglePackingNumberOn ];
  · unfold Option.getD; aesop;
    have := Finset.mem_of_max heq; aesop;
    -- Since $w$ is a subset of the triangles not sharing an edge with $e$, and $M$ is a maximal packing, we have $w.card \leq M.card - 1$.
    have h_w_card_le_M_card_minus_1 : w.card ≤ M.card - 1 := by
      exact h_max _ right_1 left;
    exact le_trans h_w_card_le_M_card_minus_1 ( by rw [ show trianglePackingNumber G = M.card from hM.2.symm ] );
  · rw [ show trianglePackingNumber G = M.card from _ ];
    · have h_max : M.card - 1 ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3 \ trianglesSharingEdge G e).powerset)).max 0 := by
        -- Since $M'$ is in the image of the cardinalities, its cardinality is one of the elements in the image.
        have hM'_in_image : M.card - 1 ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3 \ trianglesSharingEdge G e).powerset) := by
          exact Finset.mem_image.mpr ⟨ M', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hM'_subset, hM' ⟩, hM'_card ⟩;
        have := Finset.le_max hM'_in_image; aesop;
        rw [ WithBot.coe_le_iff ] at this ; aesop;
      exact Nat.sub_le_iff_le_add.mp h_max;
    · exact hM.2.symm ▸ rfl

lemma inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
      triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
  rw [ triangleCoveringNumber ];
  -- By definition of triangle covering number, we can split the covering into two parts: one covering the triangles sharing edge $e$ and the other covering the rest.
  have h_split : ∃ E1 E2 : Finset (Sym2 V), E1 ⊆ G.edgeFinset ∧ E2 ⊆ G.edgeFinset ∧ (∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E1, e ∈ t.sym2) ∧ (∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E2, e ∈ t.sym2) ∧ E1.card + E2.card ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) + triangleCoveringNumberOn G (G.cliqueFinset 3 \ trianglesSharingEdge G e) := by
    -- By definition of triangle covering number, there exist minimal covers for the triangles sharing edge $e$ and for the triangles not sharing edge $e$.
    obtain ⟨E1, hE1⟩ : ∃ E1 : Finset (Sym2 V), E1 ⊆ G.edgeFinset ∧ (∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E1, e ∈ t.sym2) ∧ E1.card = triangleCoveringNumberOn G (trianglesSharingEdge G e) := by
      -- By definition of triangleCoveringNumberOn, there exists a subset E1 of G's edges that covers all triangles in trianglesSharingEdge G e and has the minimum possible size.
      obtain ⟨E1, hE1⟩ : ∃ E1 ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2), E1.card = triangleCoveringNumberOn G (trianglesSharingEdge G e) := by
        unfold triangleCoveringNumberOn;
        have h_nonempty : Finset.Nonempty (Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset)) := by
          use G.edgeFinset;
          unfold trianglesSharingEdge; aesop;
          rcases Finset.card_eq_three.mp a.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; use s(x, y) ; aesop;
          exact a.1 ( by aesop ) ( by aesop ) ( by aesop );
        have := Finset.min_of_mem ( Finset.mem_image_of_mem Finset.card h_nonempty.choose_spec );
        obtain ⟨ b, hb ⟩ := this;
        exact Exists.elim ( Finset.mem_image.mp ( Finset.mem_of_min hb ) ) fun x hx => ⟨ x, hx.1, by aesop ⟩;
      exact ⟨ E1, Finset.mem_powerset.mp ( Finset.mem_filter.mp hE1.1 |>.1 ), Finset.mem_filter.mp hE1.1 |>.2, hE1.2 ⟩
    obtain ⟨E2, hE2⟩ : ∃ E2 : Finset (Sym2 V), E2 ⊆ G.edgeFinset ∧ (∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E2, e ∈ t.sym2) ∧ E2.card = triangleCoveringNumberOn G (G.cliqueFinset 3 \ trianglesSharingEdge G e) := by
      have h_exists_E2 : ∃ E2 : Finset (Sym2 V), E2 ⊆ G.edgeFinset ∧ (∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E2, e ∈ t.sym2) ∧ E2.card = Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset))) := by
        -- Since the set of edge covers is non-empty and finite, it must have a minimum element.
        have h_nonempty : ∃ E2 : Finset (Sym2 V), E2 ⊆ G.edgeFinset ∧ (∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E2, e ∈ t.sym2) := by
          use G.edgeFinset;
          simp +decide [ Finset.subset_iff ];
          intro t ht ht'; obtain ⟨ u, v, w, hu, hv, hw, h ⟩ := Finset.card_eq_three.mp ht.card_eq; use Sym2.mk ( u, v ) ; aesop;
          simpa using ht.1 ( by aesop ) ( by aesop ) ( by aesop );
        obtain ⟨E2, hE2⟩ : ∃ E2 ∈ Finset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset), ∀ E' ∈ Finset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset), E2.card ≤ E'.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ h_nonempty.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_nonempty.choose_spec.1, h_nonempty.choose_spec.2 ⟩ ⟩;
        use E2;
        rw [ eq_comm, Finset.min_eq_inf_withTop ];
        exact ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE2.1 |>.1 ), Finset.mem_filter.mp hE2.1 |>.2, le_antisymm ( Finset.inf_le ( Finset.mem_image_of_mem _ hE2.1 ) ) ( Finset.le_inf fun x hx => WithTop.coe_le_coe.mpr ( hE2.2 _ ( Finset.mem_image.mp hx |> Classical.choose_spec |> And.left ) |> le_trans <| Finset.mem_image.mp hx |> Classical.choose_spec |> And.right |> fun h => h.symm ▸ le_rfl ) ) ⟩;
      obtain ⟨ E2, hE2₁, hE2₂, hE2₃ ⟩ := h_exists_E2;
      use E2;
      unfold triangleCoveringNumberOn;
      rw [ ← hE2₃ ];
      exact ⟨ hE2₁, hE2₂, by rfl ⟩;
    exact ⟨ E1, E2, hE1.1, hE2.1, hE1.2.1, hE2.2.1, by rw [ hE1.2.2, hE2.2.2 ] ⟩;
  obtain ⟨ E1, E2, hE1, hE2, hE1', hE2', h ⟩ := h_split;
  have h_cover : isTriangleCover G (E1 ∪ E2) := by
    constructor <;> simp_all +decide [ Finset.subset_iff ];
    · rintro x ( hx | hx ) <;> [ exact hE1 hx; exact hE2 hx ];
    · -- By definition of $trianglesSharingEdge$, if $t$ is not in $trianglesSharingEdge G e$, then $t$ is in the set of triangles not sharing $e$.
      intros t ht
      by_cases h : t ∈ trianglesSharingEdge G e;
      · exact Exists.elim ( hE1' t h ) fun x hx => ⟨ x, Or.inl hx.1, hx.2 ⟩;
      · exact Exists.elim ( hE2' t ht h ) fun e he => ⟨ e, Or.inr he.1, he.2 ⟩;
  have h_min : (Finset.image Finset.card (Finset.filter (isTriangleCover G) (Finset.powerset G.edgeFinset))).min ≤ (E1 ∪ E2).card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.union_subset hE1 hE2 ), h_cover ⟩, rfl ⟩ );
  cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop;
  exact le_trans h_min ( le_trans ( Finset.card_union_le _ _ ) h_1 )

noncomputable section AristotleLemmas

/-
Three 3-sets pairwise intersecting in at least 2 elements either share a common pair or are all subsets of a set of size 4.
-/
lemma three_sets_structure {V : Type*} [DecidableEq V] (A B C : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3)
    (hAB : (A ∩ B).card ≥ 2) (hAC : (A ∩ C).card ≥ 2) (hBC : (B ∩ C).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ e ⊆ A ∧ e ⊆ B ∧ e ⊆ C) ∨ (A ∪ B ∪ C).card = 4 := by
      by_cases h_common_pair : ∃ x ∈ A ∩ B, x ∈ C;
      · obtain ⟨ x, hx₁, hx₂ ⟩ := h_common_pair; have := Finset.exists_mem_ne ( by linarith : 1 < Finset.card ( A ∩ B ) ) x; aesop;
        by_cases hw : w ∈ C <;> simp_all +decide [ Finset.subset_iff ];
        · exact Or.inl ⟨ { x, w }, by rw [ Finset.card_pair ( Ne.symm right_1 ) ], by aesop ⟩;
        · have := Finset.exists_mem_ne ( by linarith : 1 < Finset.card ( B ∩ C ) ) x; aesop;
          have := Finset.exists_mem_ne ( by linarith : 1 < Finset.card ( A ∩ C ) ) x; aesop;
          have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset left_1 ( Finset.insert_subset left_3 ( Finset.singleton_subset_iff.mpr left ) ) ) ; aesop;
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at this <;> aesop;
          have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ right_2, Finset.insert_subset_iff.mpr ⟨ left_2, Finset.singleton_subset_iff.mpr right ⟩ ⟩ ) ; aesop;
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at this <;> aesop;
      · -- Let $I = A \cap B$. Since $|I| = 2$, we can write $A = I \cup \{a\}$ and $B = I \cup \{b\}$ for some $a \neq b$.
        obtain ⟨I, hI⟩ : ∃ I : Finset V, I ⊆ A ∧ I ⊆ B ∧ I.card = 2 := by
          exact Exists.elim ( Finset.exists_subset_card_eq hAB ) fun I hI => ⟨ I, hI.1.trans ( Finset.inter_subset_left ), hI.1.trans ( Finset.inter_subset_right ), hI.2 ⟩
        obtain ⟨a, ha⟩ : ∃ a, A = I ∪ {a} ∧ a ∉ I := by
          obtain ⟨ a, ha ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ hI.1, by aesop_cat ⟩ ) ; use a; aesop;
          rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset left_1 left ) ] ; aesop
        obtain ⟨b, hb⟩ : ∃ b, B = I ∪ {b} ∧ b ∉ I := by
          have hB_eq : B = I ∪ (B \ I) := by
            rw [ Finset.union_sdiff_of_subset hI.2.1 ];
          have hB_card : (B \ I).card = 1 := by
            rw [ Finset.card_sdiff ] ; simp +decide [ hI, hB ];
            rw [ Finset.inter_eq_left.mpr hI.2.1, hI.2.2 ];
          obtain ⟨ b, hb ⟩ := Finset.card_eq_one.mp hB_card; use b; simp_all +singlePass ;
          rw [ Finset.ext_iff ] at hb; specialize hb b; aesop;
        have hab : a ≠ b := by
          rintro rfl; simp_all +decide ;
          exact hAC.not_lt ( lt_of_le_of_lt ( Finset.card_le_card ( show I ∩ C ⊆ ∅ from fun x hx => by aesop ) ) ( by simp +decide [ * ] ) );
        -- Since $C$ intersects $A$ and $B$ in at least 2 elements, and $a$ and $b$ are not in $C$, $C$ must contain exactly one element from $I$.
        obtain ⟨c, hc⟩ : ∃ c ∈ I, c ∈ C := by
          contrapose! hAC;
          exact lt_of_le_of_lt ( Finset.card_le_one.mpr ( by aesop ) ) ( by decide );
        exact False.elim ( h_common_pair ⟨ c, Finset.mem_inter_of_mem ( hI.1 hc.1 ) ( hI.2.1 hc.1 ), hc.2 ⟩ )

/-
If A, B, C are distinct 3-subsets of a 4-set U, and D is a 3-set intersecting each of A, B, C in at least 2 elements, then D must be a subset of U.
-/
lemma subset_of_four_set {V : Type*} [DecidableEq V] (U : Finset V) (hU : U.card = 4)
    (A B C : Finset V) (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U)
    (hA_card : A.card = 3) (hB_card : B.card = 3) (hC_card : C.card = 3)
    (h_distinct : A ≠ B ∧ A ≠ C ∧ B ≠ C)
    (D : Finset V) (hD_card : D.card = 3)
    (hDA : (D ∩ A).card ≥ 2) (hDB : (D ∩ B).card ≥ 2) (hDC : (D ∩ C).card ≥ 2) :
    D ⊆ U := by
      -- Since $K = D \cap U$ and $|D| = 3$, we have $|K| \leq 3$. If $|K| = 3$, then $D \subseteq U$.
      by_cases hK_card : (D ∩ U).card = 3;
      · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : D ∩ U ⊆ D ) ; aesop;
      · -- Since $K = D \cap U$ and $|D| = 3$, we have $|K| \leq 3$. If $|K| = 2$, then $K \subseteq A$, $K \subseteq B$, and $K \subseteq C$.
        have hK_subset_ABC : (D ∩ U) ⊆ A ∧ (D ∩ U) ⊆ B ∧ (D ∩ U) ⊆ C := by
          have hK_subset_ABC : (D ∩ U ∩ A).card ≥ 2 ∧ (D ∩ U ∩ B).card ≥ 2 ∧ (D ∩ U ∩ C).card ≥ 2 := by
            simp_all +decide [ Finset.inter_assoc, Finset.inter_left_comm, Finset.inter_comm ];
            exact ⟨ by rw [ Finset.inter_eq_right.mpr ( Finset.inter_subset_left.trans hA ) ] ; exact hDA, by rw [ Finset.inter_eq_right.mpr ( Finset.inter_subset_left.trans hB ) ] ; exact hDB, by rw [ Finset.inter_eq_right.mpr ( Finset.inter_subset_left.trans hC ) ] ; exact hDC ⟩;
          have hK_subset_ABC : (D ∩ U ∩ A).card = (D ∩ U).card ∧ (D ∩ U ∩ B).card = (D ∩ U).card ∧ (D ∩ U ∩ C).card = (D ∩ U).card := by
            have hK_subset_ABC : (D ∩ U).card ≤ 2 := by
              exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) hD_card.le ) hK_card );
            exact ⟨ le_antisymm ( Finset.card_le_card fun x hx => by aesop ) ( by linarith ), le_antisymm ( Finset.card_le_card fun x hx => by aesop ) ( by linarith ), le_antisymm ( Finset.card_le_card fun x hx => by aesop ) ( by linarith ) ⟩;
          have hK_subset_ABC : (D ∩ U ∩ A) = (D ∩ U) ∧ (D ∩ U ∩ B) = (D ∩ U) ∧ (D ∩ U ∩ C) = (D ∩ U) := by
            exact ⟨ Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith ), Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith ), Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith ) ⟩;
          grind;
        -- Since $A$, $B$, and $C$ are distinct 3-subsets of a 4-set $U$, they must be of the form $U \setminus \{x\}$, $U \setminus \{y\}$, and $U \setminus \{z\}$ for some distinct $x, y, z \in U$.
        obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ : ∃ x y z : V, x ∈ U ∧ y ∈ U ∧ z ∈ U ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ A = U \ {x} ∧ B = U \ {y} ∧ C = U \ {z} := by
          have h_form : ∀ (S : Finset V), S ⊆ U → S.card = 3 → ∃ x ∈ U, S = U \ {x} := by
            intro S hS hS_card
            have h_diff : (U \ S).card = 1 := by
              grind;
            obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp h_diff; use x; aesop;
            · exact Finset.mem_sdiff.mp ( hx.symm ▸ Finset.mem_singleton_self _ ) |>.1;
            · rw [ ← hx, Finset.sdiff_sdiff_eq_self hS ];
          obtain ⟨ x, hx, rfl ⟩ := h_form A hA hA_card; obtain ⟨ y, hy, rfl ⟩ := h_form B hB hB_card; obtain ⟨ z, hz, rfl ⟩ := h_form C hC hC_card; use x, y, z; aesop;
        -- Since $K \subseteq A$, $K \subseteq B$, and $K \subseteq C$, and $A$, $B$, and $C$ are distinct 3-subsets of a 4-set $U$, it follows that $K$ must be disjoint from $\{x, y, z\}$.
        have hK_disjoint_xyz : (D ∩ U) ⊆ U \ {x, y, z} := by
          simp_all +decide [ Finset.subset_iff ];
        have := Finset.card_le_card hK_disjoint_xyz; simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ] ;
        exact absurd this ( by linarith [ show Finset.card ( D ∩ ( U \ { x } ) ) ≤ Finset.card ( D ∩ U ) from Finset.card_mono fun x hx => by aesop ] )

end AristotleLemmas

lemma intersecting_family_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_nonempty : S.Nonempty) (hS : S ⊆ G.cliqueFinset 3)
    (h_pair : Set.Pairwise (S : Set (Finset V)) shareEdge) :
    isStar S ∨ isK4 S := by
  by_cases h_empty : S.card ≤ 1;
  · rw [ Finset.card_le_one_iff_subset_singleton ] at h_empty ; aesop;
    rcases hS with ⟨ hw₁, hw₂ ⟩;
    obtain ⟨ a, b, c, h ⟩ := Finset.card_eq_three.mp hw₂;
    exact Or.inl ⟨ { a, b }, by aesop ⟩;
  · obtain ⟨A, hA⟩ : ∃ A, A ∈ S := by
      exact hS_nonempty
    obtain ⟨B, hB, hAB⟩ : ∃ B, B ∈ S ∧ B ≠ A := by
      exact Finset.exists_mem_ne ( lt_of_not_ge h_empty ) A
    have hAB_common : ∃ e : Finset V, e.card = 2 ∧ e ⊆ A ∧ e ⊆ B := by
      have hAB_card : (A ∩ B).card ≥ 2 := by
        exact h_pair hA hB hAB.symm;
      exact Exists.elim ( Finset.exists_subset_card_eq hAB_card ) fun e he => ⟨ e, he.2, Finset.Subset.trans he.1 ( Finset.inter_subset_left ), Finset.Subset.trans he.1 ( Finset.inter_subset_right ) ⟩
    obtain ⟨e, he⟩ := hAB_common
    by_cases he_in_all : ∀ C ∈ S, e ⊆ C;
    · exact Or.inl ⟨ e, he.1, he_in_all ⟩;
    · obtain ⟨C, hC, hC_not_in_e⟩ : ∃ C ∈ S, ¬e ⊆ C := by
        exact by push_neg at he_in_all; exact he_in_all;
      have h_three_sets : (A ∪ B ∪ C).card = 4 := by
        have h_three_sets : (A ∩ B).card ≥ 2 ∧ (A ∩ C).card ≥ 2 ∧ (B ∩ C).card ≥ 2 := by
          exact ⟨ by have := h_pair hA hB; aesop, by have := h_pair hA hC; aesop, by have := h_pair hB hC; aesop ⟩;
        have h_three_sets : (∃ e : Finset V, e.card = 2 ∧ e ⊆ A ∧ e ⊆ B ∧ e ⊆ C) ∨ (A ∪ B ∪ C).card = 4 := by
          apply three_sets_structure A B C;
          all_goals simp_all +decide [ Finset.subset_iff ];
          · exact hS hA |>.2;
          · exact hS hB |>.2;
          · exact hS hC |>.2;
        aesop;
        have h_contradiction : e ⊆ A ∩ B ∧ w_1 ⊆ A ∩ B := by
          grind;
        have h_contradiction : e = A ∩ B ∧ w_1 = A ∩ B := by
          have h_contradiction : (A ∩ B).card = 2 := by
            have := hS hA; have := hS hB; simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ] ;
            have := Finset.card_le_card ( Finset.inter_subset_left : A ∩ B ⊆ A ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : A ∩ B ⊆ B ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ; );
            interval_cases _ : Finset.card ( A ∩ B ) <;> simp_all +decide;
            have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : A ∩ B ⊆ A ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : A ∩ B ⊆ B ) ; aesop;
          exact ⟨ Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ), Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ) ⟩;
        aesop;
      have h_subset_of_four_set : ∀ D ∈ S, D ⊆ A ∪ B ∪ C := by
        intros D hD
        by_cases hD_eq_A : D = A ∨ D = B ∨ D = C;
        · grind;
        · have hD_inter_A : (D ∩ A).card ≥ 2 := by
            exact h_pair hD hA ( by tauto )
          have hD_inter_B : (D ∩ B).card ≥ 2 := by
            exact h_pair hD hB ( by aesop )
          have hD_inter_C : (D ∩ C).card ≥ 2 := by
            exact h_pair hD hC ( by aesop );
          apply subset_of_four_set (A ∪ B ∪ C) h_three_sets A B C (by
          grind) (by
          grind) (by
          exact Finset.subset_union_right) (by
          have := hS hA; aesop;
          exact this.card_eq) (by
          have := hS hB; aesop;
          exact this.card_eq) (by
          have := hS hC; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.2) (by
          grind) D (by
          have := hS hD; aesop;
          exact this.card_eq) hD_inter_A hD_inter_B hD_inter_C;
      exact Or.inr ⟨ A ∪ B ∪ C, h_three_sets, h_subset_of_four_set ⟩

lemma tau_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h_star : isStar S) :
    triangleCoveringNumberOn G S ≤ 1 := by
  -- Since $S$ is a star, there exists an edge $e$ such that every triangle in $S$ contains $e$.
  obtain ⟨e, he⟩ : ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t := by
    exact h_star;
  -- Since $e$ is in $G$, we can use it as a cover. The size of this cover is 1, so the triangle covering number is at most 1.
  have h_cover : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ S, ∃ e' ∈ E', e' ∈ t.sym2) ∧ E'.card ≤ 1 := by
    obtain ⟨x, y, hxy⟩ : ∃ x y : V, x ≠ y ∧ e = {x, y} := by
      rw [ Finset.card_eq_two ] at he; tauto;
    by_cases hxy' : G.Adj x y <;> simp_all +decide [ SimpleGraph.adj_comm ];
    · refine' ⟨ { Sym2.mk ( x, y ) }, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
      exact fun t ht => ⟨ he t ht ( Finset.mem_insert_self _ _ ), he t ht ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ⟩;
    · contrapose! hxy';
      have := hS ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by rintro rfl; specialize hxy' ∅; simp_all +decide ) ) ) ; simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ] ;
      have := this.1; simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ] ;
      have := this ( show x ∈ ( Classical.choose ( Finset.nonempty_of_ne_empty ( by rintro rfl; specialize hxy' ∅; simp_all +decide ) ) : Finset V ) from by have := he _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by rintro rfl; specialize hxy' ∅; simp_all +decide ) ) ) ; aesop ) ( show y ∈ ( Classical.choose ( Finset.nonempty_of_ne_empty ( by rintro rfl; specialize hxy' ∅; simp_all +decide ) ) : Finset V ) from by have := he _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by rintro rfl; specialize hxy' ∅; simp_all +decide ) ) ) ; aesop ) ; aesop;
  unfold triangleCoveringNumberOn; aesop;
  have h_min : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ Finset.card w := by
    refine' Finset.min_le _;
    simp +zetaDelta at *;
    exact ⟨ w, ⟨ left_1, left_2 ⟩, rfl ⟩;
  cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
  exact Nat.le_trans h_min right_1

lemma covering_number_le_two_of_subset_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (s : Finset V) (hs_card : s.card = 4) (hs_contains : ∀ t ∈ S, t ⊆ s) :
    triangleCoveringNumberOn G S ≤ 2 := by
  -- Since S is a subset of the cliques in G, and each triangle in S is contained in s, which has 4 vertices, we can cover all triangles in S by selecting two edges from s.
  have h_cover : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 2 ∧ ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2 := by
    -- Since S is a subset of the cliques in G, and each triangle in S is contained in s, which has 4 vertices, we can cover all triangles in S by selecting two edges from s. Let's choose any two edges from s.
    obtain ⟨e1, e2, he1, he2, h_edges⟩ : ∃ e1 e2 : V × V, e1 ∈ s ×ˢ s ∧ e2 ∈ s ×ˢ s ∧ e1 ≠ e2 ∧ ¬(e1.1 = e1.2 ∨ e2.1 = e2.2) ∧ ∀ t ∈ S, ∃ e ∈ ({Sym2.mk e1, Sym2.mk e2} : Finset (Sym2 V)), e ∈ t.sym2 := by
      obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d : V, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
        simp_rw +decide [ Finset.card_eq_succ ] at hs_card;
        rcases hs_card with ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ ; use a, b, c, d; aesop;
      use (a, b), (c, d);
      simp_all +decide [ Finset.subset_iff ];
      intro t ht; specialize hS ht; have := Finset.card_eq_three.mp hS.2; aesop;
      have := hs_contains _ ht; simp_all +decide [ Finset.subset_iff ] ;
      have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ left, Finset.insert_subset_iff.mpr ⟨ left_1, Finset.insert_subset_iff.mpr ⟨ left_2, Finset.singleton_subset_iff.mpr left_4 ⟩ ⟩ ⟩ ) ; aesop;
    use {Sym2.mk e1, Sym2.mk e2} ∩ G.edgeFinset; aesop;
    · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by norm_num;
    · cases right_2 t a <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
      · have := hS a; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        exact ⟨ Sym2.mk ( fst, snd ), ⟨ Or.inl rfl, by have := this.1 ( by aesop : fst ∈ t ) ( by aesop : snd ∈ t ) ; aesop ⟩, by aesop ⟩;
      · have := hS a; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        exact ⟨ Sym2.mk ( fst_1, snd_1 ), ⟨ Or.inr rfl, this.1 ( by aesop ) ( by aesop ) ( by aesop ) ⟩, by aesop ⟩;
  unfold triangleCoveringNumberOn; aesop;
  have h_min_le_two : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ 2 := by
    refine' le_trans ( Finset.min_le _ ) _ <;> norm_num [ Finset.mem_image, left_1, right ];
    exacts [ w.card, ⟨ w, ⟨ left, right ⟩, rfl ⟩, left_1 ];
  cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  -- By Lemma 2.1, $S_e$ is either a star or a subset of the triangles in a $K_4$.
  have h_S_e : isStar (S_e G e M) ∨ isK4 (S_e G e M) := by
    apply intersecting_family_structure G ( S_e G e M );
    · unfold S_e;
      unfold trianglesSharingEdge; aesop;
      -- Since $e$ is in $M$ and $M$ is a triangle packing, $e$ is a triangle. Therefore, $e$ itself satisfies the condition.
      use e;
      have := hM.1.1 he; aesop;
      · exact this.card_eq.symm ▸ by decide;
      · have := hM.1.2; aesop;
    · exact Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _;
    · intro t1 ht1 t2 ht2 h; have := lemma_2_2 G M hM e he t1 t2; aesop;
  cases' h_S_e with h h;
  · have := tau_star G ( S_e G e M ) ?_ h;
    · grind;
    · exact Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _;
  · obtain ⟨ s, hs_card, hs_contains ⟩ := h;
    apply covering_number_le_two_of_subset_four G (S_e G e M) (by
    exact Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _) s hs_card hs_contains

lemma tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  -- If the packing number is zero, then there are no triangles in the graph.
  have h_no_triangles : G.cliqueFinset 3 = ∅ := by
    -- If the packing number is zero, then there are no triangles in the graph. Therefore, the cliqueFinset 3 must be empty.
    have h_no_triangles : ∀ t ∈ G.cliqueFinset 3, False := by
      unfold trianglePackingNumber at h;
      -- If the maximum size of a triangle packing is 0, then there can't be any triangles in the graph.
      have h_no_triangles : ∀ t ∈ G.cliqueFinset 3, False := by
        intro t ht
        have h_packing : isTrianglePacking G {t} := by
          unfold isTrianglePacking; aesop;
        -- Since {t} is a triangle packing, its cardinality is 1, which would mean that the maximum is at least 1. But h says the maximum is 0, which is impossible.
        have h_contra : 1 ≤ Finset.card {t} := by
          norm_num;
        have h_contra : 1 ≤ Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)) := by
          exact le_trans ( by aesop ) ( Finset.le_max ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ht ), h_packing ⟩ ) ) );
        cases h' : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
      exact h_no_triangles;
    exact Finset.eq_empty_of_forall_notMem h_no_triangles;
  unfold triangleCoveringNumber; aesop;
  rw [ Finset.min ] ; aesop;
  unfold isTriangleCover; aesop;
  rw [ Finset.inf_eq_bot_iff.mpr ] ; aesop;
  refine' ⟨ ∅, _, _ ⟩ <;> simp +decide;
  exact fun t ht => h_no_triangles t ht

/- Aristotle failed to find a proof. -/
theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end