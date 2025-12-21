/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e6fcda18-5002-4f06-b1f0-7755a91b9d97

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

- theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G
-/

/-
Tuza's Conjecture for ν ≤ 3: Final Assembly
All helper lemmas are proven. Complete the main theorem.

Key insight: We need to show τ(T_e) ≤ 2, not just τ(S_e) ≤ 2.
T_e = triangles sharing edge with packing element e
All triangles in T_e share at least one edge with e (a 3-vertex triangle).
So T_e forms a family where each element shares ≥2 vertices with e.

For the induction:
- τ(G) ≤ τ(T_e) + τ(rest) by inductive_bound
- ν(rest) = ν - 1 by lemma_2_3
- By IH: τ(rest) ≤ 2(ν-1)
- Need: τ(T_e) ≤ 2

For τ(T_e) ≤ 2:
- S_e ⊆ T_e, and we know τ(S_e) ≤ 2
- T_e \ S_e triangles share edges with OTHER packing elements
- These are covered when we cover those other elements in recursive calls
- Key: a smarter covering strategy covers T_e with ≤2 edges
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

-- All these are proven in prior Aristotle runs
lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, isMaxPacking G M := by
      -- Since the set of all triangle packings is finite, there exists a maximum packing.
      obtain ⟨M, hM⟩ : ∃ M ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G), ∀ N ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G), M.card ≥ N.card := by
        apply_rules [ Finset.exists_max_image ];
        use ∅; simp +decide [ isTrianglePacking ] ;
      simp +zetaDelta at *;
      refine' ⟨ M, hM.1.2, _ ⟩;
      rw [ eq_comm ];
      unfold trianglePackingNumber;
      rw [ Finset.max_eq_sup_coe ];
      rw [ show ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ).sup WithBot.some = WithBot.some M.card from ?_ ] ; aesop;
      refine' le_antisymm _ _ <;> aesop

lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S_e G e M → t2 ∈ S_e G e M → shareEdge t1 t2 := by
      intro t1 t2 ht1 ht2
      by_contra h_contra
      have h_not_share_edges : t1 ≠ t2 ∧ ∀ x ∈ M \ {e}, (x ∩ t1).card ≤ 1 ∧ (x ∩ t2).card ≤ 1 := by
        unfold shareEdge at h_contra; aesop;
        · unfold S_e at ht2; aesop;
          unfold trianglesSharingEdge at left; aesop;
          exact h_contra.not_le ( left.card_eq.symm ▸ by decide );
        · exact Finset.mem_filter.mp ht1 |>.2 x a a_1 |> fun h => by simpa [ Finset.inter_comm ] using h;
        · unfold S_e at ht2; aesop;
          simpa only [ Finset.inter_comm ] using right x a a_1;
      -- Let $M' = (M \setminus \{e\}) \cup \{t_1, t_2\}$.
      set M' : Finset (Finset V) := (M \ {e}) ∪ {t1, t2};
      -- We verify $M'$ is a triangle packing:
      have hM'_packing : isTrianglePacking G M' := by
        refine' ⟨ _, _ ⟩;
        · unfold S_e at *; aesop;
          simp_all +decide [ Finset.subset_iff, trianglesSharingEdge ];
          exact fun x hx hx' => hM.1.1 hx |> fun h => by aesop;
        · intro x hx y hy hxy; aesop;
          · unfold shareEdge at h_contra; aesop;
            linarith;
          · simpa only [ Finset.inter_comm ] using right _ left_1 right_1 |>.1;
          · unfold shareEdge at h_contra; aesop;
            simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ h_contra;
          · unfold S_e at ht2; aesop;
          · exact hM.1.2 ( by aesop ) ( by aesop ) ( by aesop );
      -- Now check cardinality.
      have hM'_card : M'.card = M.card + 1 := by
        have hM'_card : M'.card = (M \ {e}).card + 2 := by
          rw [ Finset.card_union_of_disjoint ] <;> aesop;
          · unfold S_e at ht1; aesop;
            unfold trianglesSharingEdge at left_1; aesop;
            specialize right_1 _ a ; simp_all +decide [ Finset.inter_comm ];
            exact Classical.not_not.1 fun h => by have := right_1 h; have := left_1.card_eq; aesop;
          · unfold S_e at ht2; aesop;
            unfold trianglesSharingEdge at left_1; aesop;
            specialize right_1 t2 a ; aesop;
            exact Classical.not_not.1 fun h => by have := right_1 h; have := left_1.card_eq; aesop;
        simp_all +decide [ Finset.card_sdiff ];
        exact Nat.succ_pred_eq_of_pos ( Finset.card_pos.mpr ⟨ e, he ⟩ );
      have hM'_max : M'.card ≤ trianglePackingNumber G := by
        have hM'_max : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
          unfold trianglePackingNumber;
          intro S hS;
          have hM'_max : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS.1, hS ⟩, rfl ⟩;
          have := Finset.le_max hM'_max; aesop;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        exact hM'_max M' hM'_packing;
      linarith [ hM.2 ]

lemma lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = trianglePackingNumber G - 1 := by
      unfold trianglePackingNumberOn trianglePackingNumber;
      -- Since $M$ is a maximum packing, removing the triangles sharing edge $e$ reduces the maximum packing number by 1.
      have h_max_packing : ∀ S : Finset (Finset V), isTrianglePacking G S → S ⊆ G.cliqueFinset 3 \ trianglesSharingEdge G e → S.card ≤ M.card - 1 := by
        intro S hS hS';
        have h_max_packing : S ∪ {e} ⊆ G.cliqueFinset 3 ∧ isTrianglePacking G (S ∪ {e}) := by
          unfold isTrianglePacking at *; aesop;
          · simp_all +decide [ Finset.subset_iff ];
            have := hM.1.1 he; aesop;
          · intro t1 ht1 t2 ht2 hne; by_cases h : t1 = e <;> by_cases h' : t2 = e <;> simp_all +decide [ Set.Pairwise ] ;
            · have := hS' ht2; simp_all +decide [ Finset.subset_iff, trianglesSharingEdge ] ;
              simpa only [ Finset.inter_comm ] using hS' ht2 |>.2 ( hS' ht2 |>.1 ) |> Nat.le_of_lt_succ;
            · have := hS' ht1; simp_all +decide [ trianglesSharingEdge ] ;
              exact Nat.le_of_lt_succ ( this.2 this.1 );
        have h_max_packing : (S ∪ {e}).card ≤ M.card := by
          have h_max_packing : ∀ S : Finset (Finset V), isTrianglePacking G S → S ⊆ G.cliqueFinset 3 → S.card ≤ M.card := by
            intros S hS hS';
            rw [ hM.2 ];
            unfold trianglePackingNumber;
            have h_max_packing : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
              exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS', hS ⟩, rfl ⟩;
            have := Finset.le_max h_max_packing; aesop;
            cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
          exact h_max_packing _ ( by tauto ) ( by tauto );
        rw [ Finset.card_union ] at h_max_packing ; aesop;
        by_cases heS : e ∈ S <;> simp_all +decide [ Finset.inter_comm ];
        · have := hS' heS; simp_all +decide [ trianglesSharingEdge ] ;
          exact absurd ( this.2 this.1 ) ( by rw [ this.1.card_eq ] ; decide );
        · exact Nat.le_sub_one_of_lt h_max_packing;
      -- Since $M$ is a maximum packing, removing the triangles sharing edge $e$ reduces the maximum packing number by 1. Therefore, there exists a packing $S$ in $G.cliqueFinset 3 \ trianglesSharingEdge G e$ with cardinality $M.card - 1$.
      obtain ⟨S, hS⟩ : ∃ S : Finset (Finset V), isTrianglePacking G S ∧ S ⊆ G.cliqueFinset 3 \ trianglesSharingEdge G e ∧ S.card = M.card - 1 := by
        refine' ⟨ M.erase e, _, _, _ ⟩ <;> simp_all +decide [ isMaxPacking ];
        · unfold isTrianglePacking at *; aesop;
          · exact Finset.Subset.trans ( Finset.erase_subset _ _ ) left;
          · exact right_1.mono fun x hx => by aesop;
        · intro t ht; aesop;
          · have := left.1 right_1; aesop;
          · have := left.2 right_1 he left_1; simp_all +decide [ trianglesSharingEdge ] ;
            linarith;
      -- Since $S$ is a packing in $G.cliqueFinset 3 \ trianglesSharingEdge G e$ with cardinality $M.card - 1$, and any other packing in this set has cardinality at most $M.card - 1$, the maximum must be $M.card - 1$.
      have h_max_eq : Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3 \ trianglesSharingEdge G e).powerset)) = some (M.card - 1) := by
        refine' le_antisymm _ _ <;> aesop;
        · exact WithBot.coe_le_coe.mpr ( h_max_packing x a_2 a_1 );
        · exact Finset.le_max ( Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr left_1, left ⟩, right ⟩ );
      unfold isMaxPacking at hM; aesop;

lemma inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
      triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
        have h_cover : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset)).min.getD 0 + (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset)).min.getD 0 := by
          obtain ⟨E1, hE1⟩ : ∃ E1 ∈ Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset, E1.card = (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset)).min.getD 0 := by
            have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2 ) G.edgeFinset.powerset ) ) from ?_ ) ; aesop;
            · replace h := Finset.mem_of_min h; aesop;
            · simp +zetaDelta at *;
              refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ trianglesSharingEdge ];
              intro t ht ht'; rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
              exact ⟨ s(a, b), by aesop ⟩;
          obtain ⟨E2, hE2⟩ : ∃ E2 ∈ Finset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset, E2.card = (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset)).min.getD 0 := by
            have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ G.cliqueFinset 3 \ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) |> Finset.Nonempty ) from ?_ );
            · rcases this with ⟨ a, ha ⟩ ; rw [ ha ] ; simp +decide [ Option.getD ] ;
              have := Finset.mem_of_min ha; aesop;
            · simp +zetaDelta at *;
              refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ trianglesSharingEdge ];
              intro t ht ht'; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hca ⟩ := Finset.card_eq_three.mp ht.2; use s(a, b); simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          use E1 ∪ E2;
          simp_all +decide [ Finset.subset_iff ];
          exact ⟨ fun x hx => hx.elim ( fun hx => hE1.1.1 hx ) fun hx => hE2.1.1 hx, fun t ht => if h : t ∈ trianglesSharingEdge G e then by obtain ⟨ e, he1, he2 ⟩ := hE1.1.2 t h; exact ⟨ e, Or.inl he1, he2 ⟩ else by obtain ⟨ e, he1, he2 ⟩ := hE2.1.2 t ht h; exact ⟨ e, Or.inr he1, he2 ⟩, le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( hE1.2.le ) ( hE2.2.le ) ) ⟩;
        obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_cover;
        refine' le_trans _ hE₃;
        have h_min : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset), x ≥ Option.getD (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)).min 0 := by
          intro x hx; have := Finset.min_le hx; aesop;
          cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop;
        exact h_min _ ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE₁, by unfold isTriangleCover; aesop ⟩ ) )

noncomputable section AristotleLemmas

/-
If three triangles pairwise share an edge, and the intersection of the first two is not contained in the third, then their union has size 4 and their common intersection has size 1.
-/
lemma intersecting_triangles_structure_aux (t1 t2 t3 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3)
    (h12 : shareEdge t1 t2) (h13 : shareEdge t1 t3) (h23 : shareEdge t2 t3)
    (hne : t1 ≠ t2)
    (h_not_star : ¬ (t1 ∩ t2) ⊆ t3) :
    (t1 ∪ t2 ∪ t3).card = 4 ∧ (t1 ∩ t2 ∩ t3).card = 1 := by
      unfold shareEdge at *;
      -- Let $e = t_1 \cap t_2$. Since $t_1 \ne t_2$ and they share an edge (intersection size $\ge 2$) and $|t_1|=3$, we must have $|e|=2$. Let $e = \{u, v\}$.
      obtain ⟨u, v, he⟩ : ∃ u v, u ≠ v ∧ t1 ∩ t2 = {u, v} := by
        have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all ( config := { decide := Bool.true } ) ; );
        interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all ( config := { decide := Bool.true } );
        · rw [ Finset.card_eq_two ] at *; tauto;
        · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; aesop;
      -- Then $t_1 = \{u, v, x\}$ and $t_2 = \{u, v, y\}$ for some $x, y$ with $x \ne y$ (since $t_1 \ne t_2$).
      obtain ⟨x, hx⟩ : ∃ x, t1 = {u, v, x} ∧ x ∉ t2 := by
        have h_t1 : t1 = {u, v} ∪ (t1 \ {u, v}) := by
          rw [ Finset.union_sdiff_of_subset ( by rw [ ← he.2 ] ; exact Finset.inter_subset_left ) ];
        have h_t1_card : (t1 \ {u, v}).card = 1 := by
          rw [ Finset.card_sdiff ] <;> simp +decide [ h1, he ];
          grind;
        obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp h_t1_card;
        grind
      obtain ⟨y, hy⟩ : ∃ y, t2 = {u, v, y} ∧ y ∉ t1 := by
        obtain ⟨y, hy⟩ : ∃ y, y ∈ t2 ∧ y ∉ t1 := by
          contrapose! hne;
          rw [ Finset.eq_of_subset_of_card_le hne ( by linarith ) ];
        use y; aesop;
        rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ show u ∈ t2 from by replace right := Finset.ext_iff.mp right u; aesop, Finset.insert_subset_iff.mpr ⟨ show v ∈ t2 from by replace right := Finset.ext_iff.mp right v; aesop, Finset.singleton_subset_iff.mpr left_2 ⟩ ⟩ ) ] ; aesop;
        rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
      -- The hypothesis `h_not_star` says $e \not\subseteq t_3$. So $t_3$ does not contain both $u$ and $v$.
      have h_not_contain_u_v : ¬(u ∈ t3 ∧ v ∈ t3) := by
        grind;
      grind

/-
If $K$ is a set of 4 vertices, and $t_1, t_2, t_3$ are three distinct triangles in $K$, then any other triangle $t$ that shares an edge with all three must also be contained in $K$.
-/
lemma k4_extension (K : Finset V) (hK : K.card = 4)
    (t1 t2 t3 : Finset V) (h1 : t1 ⊆ K) (h2 : t2 ⊆ K) (h3 : t3 ⊆ K)
    (ht1 : t1.card = 3) (ht2 : t2.card = 3) (ht3 : t3.card = 3)
    (hne12 : t1 ≠ t2) (hne13 : t1 ≠ t3) (hne23 : t2 ≠ t3)
    (t : Finset V) (ht : t.card = 3)
    (h_share1 : (t ∩ t1).card ≥ 2)
    (h_share2 : (t ∩ t2).card ≥ 2)
    (h_share3 : (t ∩ t3).card ≥ 2) :
    t ⊆ K := by
      have h_inter_card : (t1 ∩ t2 ∩ t3).card = 1 := by
        have h_inter_card : (t1 ∩ t2 ∩ t3).card = 1 := by
          have h_inter_card_aux : ∀ x y : Finset V, x ⊆ K → y ⊆ K → x.card = 3 → y.card = 3 → x ≠ y → (x ∩ y).card = 2 := by
            intros x y hx hy hx' hy' hxy
            have h_inter_card_aux : (x ∩ y).card ≥ 2 := by
              have := Finset.card_union_add_card_inter x y; simp_all +decide ;
              linarith [ show Finset.card ( x ∪ y ) ≤ 4 by exact le_trans ( Finset.card_mono ( Finset.union_subset hx hy ) ) hK.le ];
            have := Finset.card_le_card ( Finset.inter_subset_left : x ∩ y ⊆ x ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : x ∩ y ⊆ y ) ; ( have := Finset.card_le_card ( Finset.subset_union_left : x ⊆ x ∪ y ) ; ( have := Finset.card_le_card ( Finset.subset_union_right : y ⊆ x ∪ y ) ; simp_all +decide ; ) ) );
            interval_cases _ : Finset.card ( x ∩ y ) <;> simp_all +decide;
            have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : x ∩ y ⊆ x ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : x ∩ y ⊆ y ) ; aesop;
          have := Finset.card_union_add_card_inter t1 t2; have := Finset.card_union_add_card_inter ( t1 ∪ t2 ) t3; simp_all +decide ;
          rw [ show ( t1 ∪ ( t2 ∪ t3 ) ) = K from ?_ ] at this;
          · simp_all +decide [ Finset.union_inter_distrib_right ];
            have := Finset.card_union_add_card_inter ( t1 ∩ t3 ) ( t2 ∩ t3 ) ; simp_all +decide ;
            simp_all +decide [ Finset.inter_left_comm, Finset.inter_comm ];
            linarith;
          · have h_union_card : (t1 ∪ (t2 ∪ t3)).card ≤ 4 := by
              exact le_trans ( Finset.card_le_card ( Finset.union_subset h1 ( Finset.union_subset h2 h3 ) ) ) hK.le;
            have := Finset.eq_of_subset_of_card_le ( Finset.union_subset h1 ( Finset.union_subset h2 h3 ) ) ; aesop;
            exact this ( by linarith [ show ( ( t1 ∪ t2 ) ∩ t3 ).card ≤ 3 by exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht3.le ] );
        exact h_inter_card;
      -- Suppose for contradiction that $t \not\subseteq K$. Then there exists $z \in t \setminus K$.
      by_contra h_contra
      obtain ⟨z, hz⟩ : ∃ z, z ∈ t ∧ z ∉ K := by
        exact Finset.not_subset.mp h_contra;
      -- Let $S = t \cap K$. Then $|S| \le 2$.
      set S := t ∩ K
      have hS_card : S.card ≤ 2 := by
        exact Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, by aesop_cat ⟩ ) ) ( by linarith ) );
      -- Since $|S| \le 2$, we must have $|S| = 2$.
      have hS_eq_two : S.card = 2 := by
        have hS_eq_two : S.card ≥ 2 := by
          exact le_trans h_share1 ( Finset.card_mono fun x hx => Finset.mem_inter.mpr ⟨ Finset.mem_inter.mp hx |>.1, h1 ( Finset.mem_inter.mp hx |>.2 ) ⟩ );
        linarith;
      -- Since $|S| = 2$, we have $S \subseteq t1 \cap t2 \cap t3$.
      have hS_subset_inter : S ⊆ t1 ∩ t2 ∩ t3 := by
        have hS_subset_inter : t ∩ t1 ⊆ S ∧ t ∩ t2 ⊆ S ∧ t ∩ t3 ⊆ S := by
          exact ⟨ fun x hx => Finset.mem_inter.mpr ⟨ Finset.mem_of_mem_inter_left hx, Finset.mem_of_mem_inter_right hx |> fun hx' => h1 hx' ⟩, fun x hx => Finset.mem_inter.mpr ⟨ Finset.mem_of_mem_inter_left hx, Finset.mem_of_mem_inter_right hx |> fun hx' => h2 hx' ⟩, fun x hx => Finset.mem_inter.mpr ⟨ Finset.mem_of_mem_inter_left hx, Finset.mem_of_mem_inter_right hx |> fun hx' => h3 hx' ⟩ ⟩;
        have hS_eq_inter : t ∩ t1 = S ∧ t ∩ t2 = S ∧ t ∩ t3 = S := by
          exact ⟨ Finset.eq_of_subset_of_card_le hS_subset_inter.1 ( by linarith ), Finset.eq_of_subset_of_card_le hS_subset_inter.2.1 ( by linarith ), Finset.eq_of_subset_of_card_le hS_subset_inter.2.2 ( by linarith ) ⟩;
        grind;
      have := Finset.card_le_card hS_subset_inter; simp_all +decide ;

end AristotleLemmas

lemma intersecting_family_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_nonempty : S.Nonempty) (hS : S ⊆ G.cliqueFinset 3)
    (h_pair : Set.Pairwise (S : Set (Finset V)) shareEdge) :
    isStar S ∨ isK4 S := by
      by_contra! h_contra;
      -- Since S is nonempty and pairwise intersecting, there exist t1, t2, t3 in S such that t1 ≠ t2 and t1 ≠ t3.
      obtain ⟨t1, ht1⟩ : ∃ t1 ∈ S, ∃ t2 ∈ S, t1 ≠ t2 := by
        obtain ⟨ t1, ht1 ⟩ := hS_nonempty;
        by_cases h_singleton : S = {t1};
        · simp_all +decide [ isStar, isK4 ];
          obtain ⟨ a, b, c, h ⟩ := Finset.card_eq_three.mp hS.card_eq;
          exact h_contra.1 { a, b } ( by simp +decide [ h ] ) ( by simp +decide [ h ] );
        · grind;
      obtain ⟨t2, ht2, hne⟩ : ∃ t2 ∈ S, t1 ≠ t2 := ht1.right;
      obtain ⟨t3, ht3, hne3⟩ : ∃ t3 ∈ S, t3 ≠ t1 ∧ t3 ≠ t2 ∧ ¬(t1 ∩ t2 ⊆ t3) := by
        by_cases h_star : ∀ t ∈ S, t1 ∩ t2 ⊆ t;
        · refine' False.elim ( h_contra.1 ⟨ t1 ∩ t2, _, _ ⟩ );
          · have := hS ht1.1; have := hS ht2; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            have := h_pair ht1.1 ht2; simp_all +decide [ shareEdge ] ;
            have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; ( simp_all +decide [ SimpleGraph.isNClique_iff ] ; ) );
            interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
            have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; aesop;
          · exact h_star;
        · grind +ring;
      -- Let $K = t1 \cup t2 \cup t3$. We get $|K|=4$.
      obtain ⟨K, hK⟩ : ∃ K : Finset V, K.card = 4 ∧ t1 ⊆ K ∧ t2 ⊆ K ∧ t3 ⊆ K := by
        have hK : (t1 ∪ t2 ∪ t3).card = 4 := by
          apply (intersecting_triangles_structure_aux t1 t2 t3 (by
          have := hS ht1.1; aesop;
          exact this.2) (by
          have := hS ht2; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.2) (by
          have := hS ht3; aesop;
          exact this.card_eq) (by
          exact h_pair ht1.1 ht2 hne) (by
          exact h_pair ht1.1 ht3 ( by tauto )) (by
          exact h_pair ht2 ht3 ( by tauto )) (by
          tauto) (by
          tauto)).left;
        exact ⟨ _, hK, Finset.subset_union_left.trans ( Finset.subset_union_left ), Finset.subset_union_right.trans ( Finset.subset_union_left ), Finset.subset_union_right ⟩;
      -- Now for any $t \in S$, $t$ shares an edge with $t1, t2, t3$.
      have h_share : ∀ t ∈ S, (t ∩ t1).card ≥ 2 ∧ (t ∩ t2).card ≥ 2 ∧ (t ∩ t3).card ≥ 2 := by
        intro t ht
        have h_share1 : (t ∩ t1).card ≥ 2 := by
          by_cases h : t = t1 <;> simp_all +decide [ Set.Pairwise ];
          · have := hS ht1.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            exact this.card_eq.symm ▸ by decide;
          · exact h_pair ht ht1.1 h
        have h_share2 : (t ∩ t2).card ≥ 2 := by
          by_cases h : t = t2 <;> simp_all +decide [ shareEdge ];
          · have := hS ht2; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            exact this.card_eq.symm ▸ by decide;
          · exact h_pair ht ht2 h
        have h_share3 : (t ∩ t3).card ≥ 2 := by
          have := h_pair ( show t ∈ S from ht ) ( show t3 ∈ S from ht3 ) ; aesop;
          by_cases h : t = t3 <;> aesop;
          have := hS ht3; aesop;
          exact this.card_eq.symm ▸ by decide;
        exact ⟨h_share1, h_share2, h_share3⟩;
      -- Apply `k4_extension` with $K, t1, t2, t3, t$.
      have h_subset_K : ∀ t ∈ S, t ⊆ K := by
        intros t ht
        apply k4_extension K hK.left t1 t2 t3 hK.right.left hK.right.right.left hK.right.right.right;
        all_goals have := hS ht1.1; have := hS ht2; have := hS ht3; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        all_goals have := hS ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        · grind;
        · grind;
      refine' h_contra.2 ⟨ K, hK.1, fun t ht => h_subset_K t ht ⟩

lemma tau_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h_star : isStar S) :
    triangleCoveringNumberOn G S ≤ 1 := by
      unfold triangleCoveringNumberOn;
      have h_min : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 1 := by
        obtain ⟨ e, he, he' ⟩ := h_star;
        obtain ⟨ u, v, huv ⟩ := Finset.card_eq_two.mp he;
        by_cases huv' : G.Adj u v <;> simp_all +decide [ Finset.subset_iff ];
        · refine' ⟨ { Sym2.mk ( u, v ) }, _, _, _ ⟩ <;> aesop;
        · contrapose! hS;
          rcases S.eq_empty_or_nonempty with ( rfl | ⟨ t, ht ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          · exact absurd ( hS ∅ ) ( by simp +decide );
          · exact ⟨ t, ht, fun h => by have := h ( he' t ht |>.1 ) ( he' t ht |>.2 ) ; aesop ⟩;
      aesop;
      have h_min : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ w.card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ w, by aesop ⟩ );
      exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop ) ( Nat.cast_le.mpr right )

lemma covering_number_le_two_of_subset_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (s : Finset V) (hs_card : s.card = 4) (hs_contains : ∀ t ∈ S, t ⊆ s) :
    triangleCoveringNumberOn G S ≤ 2 := by
      unfold triangleCoveringNumberOn;
      have h_edges_s : ∃ E' ∈ Finset.powerset (G.edgeFinset), (∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 2 := by
        -- Since $s$ is a set of 4 vertices, the triangles in $S$ are subsets of $s$ with 3 elements. The edges in $s$ are the pairs of vertices in $s$. There are 6 edges in $s$, and any two edges in $s$ cover all triangles in $S$.
        have h_edges_s : ∀ t ∈ S, t.card = 3 := by
          intro t ht; specialize hS ht; aesop;
          exact hS.card_eq;
        -- Let $a, b, c, d$ be the vertices of $s$. Any triangle in $S$ must be one of the four possible triangles formed by these vertices: $\{a, b, c\}$, $\{a, b, d\}$, $\{a, c, d\}$, or $\{b, c, d\}$.
        obtain ⟨a, b, c, d, hs⟩ : ∃ a b c d : V, s = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
          simp_rw +decide [ Finset.card_eq_succ ] at hs_card;
          obtain ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ := hs_card; use a, b, c, d; aesop;
        -- Any triangle in $S$ must be one of the four possible triangles formed by these vertices: $\{a, b, c\}$, $\{a, b, d\}$, $\{a, c, d\}$, or $\{b, c, d\}$.
        have h_triangles : ∀ t ∈ S, t = {a, b, c} ∨ t = {a, b, d} ∨ t = {a, c, d} ∨ t = {b, c, d} := by
          intro t ht
          have ht_subset : t ⊆ {a, b, c, d} := by
            exact hs.1 ▸ hs_contains t ht
          have ht_card : t.card = 3 := by
            exact h_edges_s t ht
          have ht_cases : t = {a, b, c} ∨ t = {a, b, d} ∨ t = {a, c, d} ∨ t = {b, c, d} := by
            rw [ Finset.card_eq_three ] at ht_card;
            rcases ht_card with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
            rcases ht_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hxy hxz hyz ⊢
          exact ht_cases;
        by_cases hab : G.Adj a b <;> by_cases hcd : G.Adj c d <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
        · refine' ⟨ { Sym2.mk ( a, b ), Sym2.mk ( c, d ) }, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
          grind;
        · refine' ⟨ { Sym2.mk ( a, b ) }, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
          intro t ht; specialize h_triangles t ht; aesop;
          · have := hS ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          · have := hS ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        · use {Sym2.mk (c, d)}; simp_all +decide [ Set.subset_def ] ;
          intro t ht; specialize h_triangles t ht; aesop;
          · have := hS ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          · have := hS ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        · use ∅; simp_all +decide [ SimpleGraph.IsNClique ] ;
          intro t ht; specialize hS ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          rcases h_triangles t ht with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.isClique_iff ];
      aesop;
      have h_min_le : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ Finset.card w := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ w, by aesop ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
      exact Nat.le_trans h_min_le right

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
      have h_star_or_k4 : isStar (S_e G e M) ∨ isK4 (S_e G e M) := by
        apply intersecting_family_structure G (S_e G e M) (by
        -- Since $e \in M$ and $M$ is a triangle packing, $e$ is a triangle in $G$. Therefore, $e \in S_e G e M$.
        use e
        simp [S_e, he];
        have := hM.1.1 he; aesop;
        · unfold trianglesSharingEdge; aesop;
          exact this.card_eq.ge.trans' ( by decide );
        · have := hM.1.2; aesop;) (by
        exact fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1) (by
        intro t1 ht1 t2 ht2 hne; exact lemma_2_2 G M hM e he t1 t2 ht1 ht2;);
      -- If $S_e$ is a star, then by Lemma 2.4, $\tau^*(S_e) \leq 1$.
      by_cases h_star : isStar (S_e G e M);
      · exact le_trans ( tau_star G ( S_e G e M ) ( by
          exact Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _ ) h_star ) ( by norm_num );
      · -- If $S_e$ is a $K_4$, then by Lemma 2.5, $\tau^*(S_e) \leq 2$.
        obtain ⟨s, hs_card, hs_contains⟩ := h_star_or_k4.resolve_left h_star
        have h_covering : triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
          apply covering_number_le_two_of_subset_four G (S_e G e M) (by
          exact fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1) s hs_card hs_contains
        exact h_covering

lemma tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
      -- If the triangle packing number is zero, then there are no triangles in the graph.
      have h_no_triangles : ∀ t ∈ G.cliqueFinset 3, False := by
        -- Since the packing number is zero, any subset of triangles must be empty. Therefore, for any t in the cliqueFinset 3, the subset {t} would have a cardinality of 1, which is greater than 0. This contradicts the definition of the packing number being zero. Therefore, there can't be any triangles in the cliqueFinset 3.
        intros t ht
        have h_subset : {t} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
          simp_all +decide [ isTrianglePacking ];
        unfold trianglePackingNumber at h;
        have h_card : (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max ≥ 1 := by
          exact Finset.le_max ( Finset.mem_image.mpr ⟨ { t }, h_subset, by simp +decide ⟩ );
        cases h' : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
      unfold triangleCoveringNumber; aesop;
      -- Since there are no triangles in G, the empty set is a triangle cover.
      have h_empty_cover : isTriangleCover G ∅ := by
        exact ⟨ Finset.empty_subset _, fun t ht => False.elim ( h_no_triangles t <| by simpa using ht ) ⟩;
      -- Since the empty set is a triangle cover, the minimum cardinality of a triangle cover is 0.
      have h_min_zero : 0 ∈ Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset) := by
        aesop;
      have h_min_zero : Finset.min (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)) ≤ 0 := by
        exact Finset.min_le h_min_zero;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop

/- Aristotle failed to find a proof. -/
-- Need this lemma: τ(T_e) ≤ 2
-- T_e triangles all share an edge with packing element e (which is a triangle)
-- Since e has 3 edges, T_e triangles share one of these 3 edges with e
-- So T_e is covered by the 3 edges of e, meaning τ(T_e) ≤ 3
-- But with care we can show τ(T_e) ≤ 2 via the star/K4 structure
lemma tau_T_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by sorry

noncomputable section AristotleLemmas

#check Finset.sym2

lemma tau_on_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (S1 S2 : Finset (Finset V)) (h_subset : S1 ⊆ S2) (h_S2 : S2 ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G S1 ≤ triangleCoveringNumberOn G S2 := by
      unfold triangleCoveringNumberOn;
      unfold Option.getD; aesop;
      · -- Since the set for $S_2$ is a subset of the set for $S_1$, the minimum of the set for $S_1$ is less than or equal to the minimum of the set for $S_2$.
        have h_subset : Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S2, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}) ⊆ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S1, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}) := by
          grind;
        have := Finset.min_le_of_eq ( h_subset <| Finset.mem_coe.mpr <| Finset.mem_of_min heq_1 ) heq; aesop;
      · -- Since the minimum of the image of the cardinalities of the sets in S2 is none, this implies that the set is empty, which contradicts the fact that S2 is a subset of the cliqueFinset 3.
        have h_empty : {E' ∈ G.edgeFinset.powerset | ∀ t ∈ S2, ∃ e ∈ E', ∀ a ∈ e, a ∈ t} = ∅ := by
          -- If the minimum of the image of the cardinalities of the sets in S2 is none, then the set must be empty.
          have h_empty : ∀ {s : Finset (Finset (Sym2 V))}, (Finset.image Finset.card s).min = Option.none → s = ∅ := by
            simp +contextual [ Finset.ext_iff, WithTop.none_eq_top ];
          exact h_empty heq_1;
        simp_all +decide [ Finset.ext_iff ];
        contrapose! h_empty;
        refine' ⟨ G.edgeFinset, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        intro t ht; specialize h_S2 ht; rw [ SimpleGraph.isNClique_iff ] at h_S2; aesop;
        rcases Finset.card_eq_three.mp right with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use Sym2.mk ( u, v ) ; aesop

lemma nu_on_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h : trianglePackingNumberOn G S = 0) :
    triangleCoveringNumberOn G S = 0 := by
      unfold trianglePackingNumberOn at h
      unfold triangleCoveringNumberOn at *;
      -- Since the maximum of the cardinalities of the triangle packings is zero, there are no triangles in S. Therefore, the minimum of the cardinalities of the edge subsets that cover S is also zero.
      have h_empty : S = ∅ := by
        contrapose! h; simp_all +decide [ isTrianglePacking ] ;
        -- Since $S$ is non-empty, there exists at least one triangle in $S$.
        obtain ⟨t, ht⟩ : ∃ t ∈ S, isTrianglePacking G {t} := by
          exact Exists.elim ( Finset.nonempty_of_ne_empty h ) fun t ht => ⟨ t, ht, by rw [ isTrianglePacking ] ; exact ⟨ by simpa using hS ht, by simp +decide ⟩ ⟩;
        -- Since {t} is a triangle packing, its cardinality is 1, which is greater than 0.
        have h_card : 1 ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) S.powerset) := by
          exact Finset.mem_image.mpr ⟨ { t }, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ht.1 ), ht.2 ⟩, by simp +decide ⟩;
        have h_max : (Finset.image Finset.card (Finset.filter (isTrianglePacking G) S.powerset)).max ≥ 1 := by
          exact Finset.le_max h_card |> le_trans ( by norm_num );
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) S.powerset ) ) <;> aesop;
      aesop;
      rw [ Finset.min_eq_inf_withTop ] ; aesop;
      rw [ Finset.inf_eq_iInf ] ; aesop;
      rw [ show ( ⨅ a : Finset ( Sym2 V ), ⨅ ( _ : ( a : Set ( Sym2 V ) ) ⊆ G.edgeSet ), ( a.card : WithTop ℕ ) ) = ⊥ from ?_ ] ; simp +decide [ Option.getD ];
      exact le_antisymm ( iInf_le_of_le ∅ <| by simp +decide ) ( by exact le_iInf fun _ => le_iInf fun _ => Nat.cast_nonneg _ )

lemma nu_on_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h : trianglePackingNumberOn G S = 1) :
    triangleCoveringNumberOn G S ≤ 2 := by
      revert h;
      intro h
      have h_star_or_k4 : isStar S ∨ isK4 S := by
        apply intersecting_family_structure G S (by
        contrapose! h; aesop;
        unfold trianglePackingNumberOn at a ; aesop;
        simp_all +decide [ Finset.filter_singleton, isTrianglePacking ]) hS (by
        -- Since the maximum packing number is 1, any two elements in S must share an edge.
        have h_pairwise : ∀ t1 t2 : Finset V, t1 ∈ S → t2 ∈ S → t1 ≠ t2 → (t1 ∩ t2).card ≥ 2 := by
          intro t1 t2 ht1 ht2 hne
          by_contra h_contra
          have h_packing : ∃ M : Finset (Finset V), M ⊆ S ∧ M.card ≥ 2 ∧ isTrianglePacking G M := by
            use {t1, t2};
            unfold isTrianglePacking; aesop;
            · aesop_cat;
            · exact Finset.insert_subset_iff.mpr ⟨ hS ht1, Finset.singleton_subset_iff.mpr ( hS ht2 ) ⟩;
            · intro x hx y hy hxy; aesop;
              · linarith;
              · rwa [ Finset.inter_comm, Nat.lt_succ_iff ] at h_contra;
          -- Since the maximum packing number is 1, any packing must have a cardinality of at most 1. But h_packing gives us a packing with cardinality at least 2, which is a contradiction.
          have h_contra : ∀ M : Finset (Finset V), M ⊆ S → isTrianglePacking G M → M.card ≤ 1 := by
            unfold trianglePackingNumberOn at h; aesop;
            have h_contra : ∀ M : Finset (Finset V), M ⊆ S → isTrianglePacking G M → M.card ≤ 1 := by
              intro M hM hP
              have h_max : M.card ≤ Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) S.powerset)) := by
                exact Finset.le_max ( Finset.mem_image.mpr ⟨ M, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hM, hP ⟩, rfl ⟩ )
              cases h' : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) S.powerset ) ) <;> aesop;
            exact h_contra M a a_1;
          exact not_lt_of_ge ( h_contra _ h_packing.choose_spec.1 h_packing.choose_spec.2.2 ) h_packing.choose_spec.2.1;
        exact fun x hx y hy hxy => h_pairwise x y hx hy hxy);
      aesop;
      · exact le_trans ( tau_star _ _ hS h_1 ) ( by decide );
      · -- Since S is a subset of a K4, we can apply the lemma covering_number_le_two_of_subset_four.
        obtain ⟨s, hs_card, hs_contains⟩ := h_2;
        exact covering_number_le_two_of_subset_four G S hS s hs_card hs_contains

lemma tau_on_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (S1 S2 : Finset (Finset V)) (h_S1 : S1 ⊆ G.cliqueFinset 3) (h_S2 : S2 ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (S1 ∪ S2) ≤ triangleCoveringNumberOn G S1 + triangleCoveringNumberOn G S2 := by
      -- Let $E_1$ be a minimal edge set covering $S_1$ and $E_2$ be a minimal edge set covering $S_2$.
      obtain ⟨E1, hE1⟩ : ∃ E1 : Finset (Sym2 V), E1 ⊆ G.edgeFinset ∧ (∀ t ∈ S1, ∃ e ∈ E1, e ∈ t.sym2) ∧ E1.card = triangleCoveringNumberOn G S1 := by
        unfold triangleCoveringNumberOn;
        have := Finset.min_of_mem ( Finset.mem_image_of_mem Finset.card <| show G.edgeFinset ∈ Finset.filter ( fun E' => ∀ t ∈ S1, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) from Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.Subset.refl _, fun t ht => by
                                                                            have := h_S1 ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
                                                                            obtain ⟨ v, hv, w, hw, h ⟩ := Finset.card_eq_three.mp this.2; use s(v, w); aesop;
                                                                            have := this.1; aesop; ⟩ ) ; aesop;
        have := Finset.mem_of_min h; aesop;
      obtain ⟨E2, hE2⟩ : ∃ E2 : Finset (Sym2 V), E2 ⊆ G.edgeFinset ∧ (∀ t ∈ S2, ∃ e ∈ E2, e ∈ t.sym2) ∧ E2.card = triangleCoveringNumberOn G S2 := by
        unfold triangleCoveringNumberOn;
        have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S2, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ).Nonempty from ?_ );
        · obtain ⟨ a, ha ⟩ := this; rcases Finset.mem_image.mp ( Finset.mem_of_min ha ) with ⟨ E2, hE2, rfl ⟩ ; use E2; aesop;
        · simp;
          refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ h_S2 ];
          intro t ht; have := h_S2 ht; simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ] ;
          rcases this with ⟨ h1, h2 ⟩ ; rcases Finset.one_lt_card.1 ( by linarith ) with ⟨ x, hx, y, hy, hxy ⟩ ; use Sym2.mk ( x, y ) ; aesop;
      refine' le_trans _ ( Finset.card_union_le _ _ ) |> le_trans <| add_le_add hE1.2.2.le hE2.2.2.le;
      unfold triangleCoveringNumberOn; aesop;
      -- Since $E1 \cup E2$ is in the image of the cardinalities of the edge sets that cover $S1 \cup S2$, its cardinality is an upper bound for the minimum.
      have h_union_in_image : (E1 ∪ E2).card ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ (t : Finset V), t ∈ S1 ∨ t ∈ S2 → ∃ e ∈ E', ∀ a ∈ e, a ∈ t}) := by
        norm_num +zetaDelta at *;
        exact ⟨ E1 ∪ E2, ⟨ by aesop_cat, fun t ht => by cases ht <;> [ exact Exists.elim ( left_2 t ‹_› ) fun e he => ⟨ e, Finset.mem_union_left _ he.1, he.2 ⟩ ; exact Exists.elim ( left_3 t ‹_› ) fun e he => ⟨ e, Finset.mem_union_right _ he.1, he.2 ⟩ ] ⟩, rfl ⟩;
      have := Finset.min_le h_union_in_image; aesop;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t : Finset V, t ∈ S1 ∨ t ∈ S2 → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

lemma nu_on_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = trianglePackingNumberOn G S) (hM_subset : M ⊆ S)
    (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G (S \ trianglesSharingEdge G e) = trianglePackingNumberOn G S - 1 := by
      -- Since $e$ is in $M$ and $M$ is a maximum packing, removing $e$ from $S$ reduces the maximum packing size by 1. This follows from the fact that $M$ is a maximum packing and $e$ is part of $M$.
      have h_max_packing : trianglePackingNumberOn G (S \ trianglesSharingEdge G e) ≥ trianglePackingNumberOn G S - 1 := by
        have h_max_packing : ∃ M' : Finset (Finset V), M' ⊆ S \ trianglesSharingEdge G e ∧ M'.card ≥ M.card - 1 ∧ isTrianglePacking G M' := by
          refine' ⟨ M \ { e }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
          · unfold trianglesSharingEdge; aesop;
            exact lt_of_le_of_lt ( hM.2 a he a_1 ) ( by decide );
          · grind;
          · exact ⟨ Finset.Subset.trans ( Finset.sdiff_subset ) hM.1, fun x hx y hy hxy => hM.2 ( Finset.mem_sdiff.mp hx |>.1 ) ( Finset.mem_sdiff.mp hy |>.1 ) hxy ⟩;
        aesop;
        refine' le_trans left_1 _;
        unfold trianglePackingNumberOn; aesop;
        have h_max_packing : w.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (S \ trianglesSharingEdge G e).powerset) := by
          aesop;
        have := Finset.le_max h_max_packing; aesop;
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( S \ trianglesSharingEdge G e ).powerset ) ) <;> aesop;
      -- Let $M'$ be a maximum packing on $S \setminus T_e$. Then $M' \cup \{e\}$ is a packing on $S$.
      have h_max_packing_union : ∀ M' : Finset (Finset V), M' ⊆ S \ trianglesSharingEdge G e → isTrianglePacking G M' → trianglePackingNumberOn G S ≥ M'.card + 1 := by
        intros M' hM'_subset hM'_packing
        have h_max_packing_union : isTrianglePacking G (M' ∪ {e}) := by
          refine' ⟨ _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, isTrianglePacking ];
          simp_all +decide [ Set.Pairwise, Finset.disjoint_left ];
          simp_all +decide [ Finset.inter_comm, trianglesSharingEdge ];
          exact ⟨ fun x hx hx' => Nat.le_of_lt_succ ( hM'_subset hx |>.2 ), fun x hx hx' => Nat.le_of_lt_succ ( hM'_subset hx |>.2 ) ⟩;
        have h_max_packing_union : trianglePackingNumberOn G S ≥ (M' ∪ {e}).card := by
          have h_max_packing_union : M' ∪ {e} ⊆ S := by
            grind;
          unfold trianglePackingNumberOn at *; aesop;
          unfold Option.getD; aesop;
          have := Finset.le_max_of_eq ( Finset.mem_image_of_mem Finset.card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_max_packing_union, h_max_packing_union_1 ⟩ ) ) heq; aesop;
        by_cases heM' : e ∈ M' <;> simp_all +decide [ Finset.inter_comm ];
        have := hM'_subset heM'; simp_all +decide [ trianglesSharingEdge ] ;
        have := hM.1 he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      refine' le_antisymm _ h_max_packing;
      unfold trianglePackingNumberOn at *;
      unfold Option.getD at *; aesop;
      have := Finset.mem_of_max heq; aesop;
      exact Nat.le_sub_one_of_lt ( h_max_packing_union w left right_1 )

lemma extend_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (M' : Finset (Finset V)) (hM' : isTrianglePacking G M')
    (h_disjoint : M' ⊆ (G.cliqueFinset 3) \ (trianglesSharingEdge G e)) :
    isTrianglePacking G (insert e M') ∧ (insert e M').card = M'.card + 1 := by
      unfold isTrianglePacking at *; aesop;
      · simp_all +decide [ Finset.subset_iff ];
      · intro t1 ht1 t2 ht2 h; cases' ht1 with ht1 ht1 <;> cases' ht2 with ht2 ht2 <;> aesop;
        · have := h_disjoint ht2; simp_all +decide [ trianglesSharingEdge ] ;
          simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( this.2 this.1 );
        · have := h_disjoint ht1; simp_all +decide [ trianglesSharingEdge ] ;
          exact Nat.le_of_lt_succ ( this.2 this.1 );
      · rw [ Finset.card_insert_of_notMem ];
        intro h; specialize h_disjoint h; simp_all +decide [ trianglesSharingEdge ] ;
        exact h_disjoint.not_le ( by have := he.card_eq; aesop )

end AristotleLemmas

theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  interval_cases _ : trianglePackingNumber G <;> simp_all +decide only [];
  · have := tuza_case_nu_0 G ‹_›; aesop;
  · -- Apply the lemma nu_on_one with S = G.cliqueFinset 3.
    have h_tau_le_2 : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 2 := by
      apply nu_on_one G ( G.cliqueFinset 3 ) ( Finset.Subset.refl _ );
      unfold trianglePackingNumber trianglePackingNumberOn at * ; aesop;
    unfold triangleCoveringNumber;
    unfold triangleCoveringNumberOn at h_tau_le_2;
    convert h_tau_le_2 using 4;
    unfold isTriangleCover; aesop;
  · -- Let $M$ be a max packing of $G$. Pick $e \in M$.
    obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), isMaxPacking G M ∧ M.card = 2 := by
      have := exists_max_packing G; aesop;
      exact ⟨ w, h, by linarith [ h.2 ] ⟩;
    -- By `inductive_bound`, `tau(G) <= tau(T_e) + tau(G \ T_e)`.
    have h_inductive : triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card)))) + triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card))))) := by
      apply inductive_bound G M hM.left (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card))) (Classical.choose_spec (Finset.card_pos.mp (by linarith : 0 < M.card)));
    -- By `nu_on_step`, `nu(G \ T_e) = nu(G) - 1 = 1`.
    have h_nu_G_minus_T_e : trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card))))) = 1 := by
      convert lemma_2_3 G M hM.1 ( Classical.choose ( Finset.card_pos.mp ( by linarith : 0 < M.card ) ) ) ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith : 0 < M.card ) ) ) using 1;
      grind;
    -- By `nu_on_one`, `tau(G \ T_e) <= 2`.
    have h_tau_G_minus_T_e : triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card))))) ≤ 2 := by
      apply nu_on_one G (G.cliqueFinset 3 \ trianglesSharingEdge G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card)))) (by
      grind) h_nu_G_minus_T_e;
    -- By `tau_T_e_le_2`, `tau(T_e) <= 2`.
    have h_tau_T_e : triangleCoveringNumberOn G (trianglesSharingEdge G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card)))) ≤ 2 := by
      apply tau_T_e_le_2 G M hM.left (Classical.choose (Finset.card_pos.mp (by linarith : 0 < M.card))) (Classical.choose_spec (Finset.card_pos.mp (by linarith : 0 < M.card)))
    linarith [h_inductive, h_tau_G_minus_T_e, h_tau_T_e];
  · -- Let `M` be a max packing of `G`. Pick `e \in M`.
    obtain ⟨M, hM⟩ : ∃ M, isMaxPacking G M ∧ M.card = 3 := by
      have := exists_max_packing G; aesop;
      exact ⟨ w, h, by rw [ ← ‹trianglePackingNumber G = 3›, h.2 ] ⟩
    obtain ⟨e, he⟩ : ∃ e ∈ M, True := by
      exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hx, trivial ⟩
    have h_inductive_bound : triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) + triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
      apply inductive_bound G M hM.left e he.left
    have h_tau_T_e : triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
      apply tau_T_e_le_2 G M hM.left e he.left
    have h_tau_G_minus_T_e : triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) ≤ 4 := by
      -- Let `S' = (G.cliqueFinset 3) \ T_e`. We need to show `tau(S') <= 4`.
      set S' := (G.cliqueFinset 3) \ (trianglesSharingEdge G e)
      have h_nu_S' : trianglePackingNumberOn G S' = 2 := by
        have := lemma_2_3 G M hM.1 e he.1; aesop;
      have h_tau_S' : triangleCoveringNumberOn G S' ≤ 4 := by
        -- Let `M'` be a max packing of `S'` (subset of `S'`). Pick `e' \in M'`.
        obtain ⟨M', hM', hM'_card⟩ : ∃ M', isTrianglePacking G M' ∧ M' ⊆ S' ∧ M'.card = 2 := by
          have h_exists_M' : ∃ M' ∈ (S'.powerset.filter (isTrianglePacking G)), M'.card = 2 := by
            unfold trianglePackingNumberOn at h_nu_S'; aesop;
            have := Finset.mem_of_max ( show ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( Finset.powerset S' ) ) ).max = some 2 from by { rw [ Option.getD_eq_iff ] at h_nu_S'; aesop } ) ; aesop;
          grind
        obtain ⟨e', he'⟩ : ∃ e' ∈ M', True := by
          exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hx, trivial ⟩
        have h_inductive_bound_S' : triangleCoveringNumberOn G S' ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e' ∩ S') + triangleCoveringNumberOn G (S' \ (trianglesSharingEdge G e' ∩ S')) := by
          have h_inductive_bound_S' : triangleCoveringNumberOn G S' ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e' ∩ S') + triangleCoveringNumberOn G (S' \ (trianglesSharingEdge G e' ∩ S')) := by
            have h_union : S' = (trianglesSharingEdge G e' ∩ S') ∪ (S' \ (trianglesSharingEdge G e' ∩ S')) := by
              ext t; by_cases ht : t ∈ trianglesSharingEdge G e' <;> aesop;
            convert tau_on_union G _ _ _ _ using 2;
            · exact h_union;
            · exact Finset.inter_subset_right.trans ( Finset.sdiff_subset );
            · exact fun x hx => Finset.mem_sdiff.mp hx |>.1 |> Finset.mem_sdiff.mp |>.1
          exact h_inductive_bound_S'
        have h_tau_T_e'_S' : triangleCoveringNumberOn G (trianglesSharingEdge G e' ∩ S') ≤ 2 := by
          have h_tau_T_e'_S' : triangleCoveringNumberOn G (trianglesSharingEdge G e') ≤ 2 := by
            apply tau_T_e_le_2;
            -- Since $M'$ is a packing in $S'$ and has cardinality 2, we can add $e$ to $M'$ to get a packing of size 3.
            have h_extend : isTrianglePacking G (insert e M') ∧ (insert e M').card = 3 := by
              bound;
              · exact extend_packing G e ( by
                  have := left.1; aesop;
                  exact Finset.mem_coe.mp ( this.1 left_1 ) |> fun h => by simpa using h; ) M' hM' ( by
                  exact left_2 ) |>.1
                skip;
              · rw [ Finset.card_insert_of_notMem ] <;> aesop;
                have := left_2 a; simp_all +decide [ trianglesSharingEdge ] ;
                exact absurd ( this.2 this.1 ) ( by rw [ this.1.card_eq ] ; decide );
            exact ⟨ h_extend.1, by linarith ⟩;
            exact Finset.mem_insert_of_mem he'.1
          exact le_trans (tau_on_mono G (trianglesSharingEdge G e' ∩ S') (trianglesSharingEdge G e') (by
          exact Finset.inter_subset_left) (by
          exact Finset.filter_subset _ _)) h_tau_T_e'_S'
        have h_tau_G_minus_T_e'_S' : triangleCoveringNumberOn G (S' \ (trianglesSharingEdge G e' ∩ S')) ≤ 2 := by
          have h_nu_G_minus_T_e'_S' : trianglePackingNumberOn G (S' \ (trianglesSharingEdge G e' ∩ S')) = 1 := by
            have := nu_on_step G S' M' hM' ( by aesop ) ( by aesop ) e' he'.1; aesop;
          have h_tau_G_minus_T_e'_S' : triangleCoveringNumberOn G (S' \ (trianglesSharingEdge G e' ∩ S')) ≤ 2 := by
            apply nu_on_one G (S' \ (trianglesSharingEdge G e' ∩ S')) (by
            exact fun x hx => Finset.mem_sdiff.mp ( Finset.mem_sdiff.mp hx |>.1 ) |>.1 |> fun hx' => by aesop;) h_nu_G_minus_T_e'_S' |> le_trans <| by
              norm_num +zetaDelta at *
            skip
          exact h_tau_G_minus_T_e'_S'
        linarith [h_inductive_bound_S', h_tau_T_e'_S', h_tau_G_minus_T_e'_S']
      exact h_tau_S'
    linarith [h_inductive_bound, h_tau_T_e, h_tau_G_minus_T_e]

end