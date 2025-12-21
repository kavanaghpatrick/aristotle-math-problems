/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: caefde68-6beb-4ba7-ba1c-bb1ecf1088b2

The following was proved by Aristotle:

- theorem tau_Te_counterexample :
    ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
      (e : Finset V) (he : e ∈ M),
    coveringNumberOn G (T_e G e) ≥ 3
-/

/-
Tuza ν ≤ 3: PESSIMIST - Hunt for counterexamples to τ(T_e) ≤ 2

We claim: For e ∈ M (max packing) with |M| ≤ 3, τ(T_e) ≤ 2.

This file asks Aristotle to DISPROVE this by finding:
- A graph G with ν(G) ≤ 3
- A max packing M with some e ∈ M
- Where τ(T_e) ≥ 3

If Aristotle proves the negation, our proof strategy is INVALID.
If Aristotle fails, it provides evidence the lemma might be true.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

noncomputable section AristotleLemmas

abbrev V_ex := Fin 5
def G_ex : SimpleGraph V_ex := ⊤
def M_ex : Finset (Finset V_ex) := { {0,1,2}, {0,3,4} }
def e_ex : Finset V_ex := {0,1,2}

lemma M_ex_subset : M_ex ⊆ G_ex.cliqueFinset 3 := by
  -- Since $M_ex$ only contains the triangle $\{1, 2, 3\}$, we need to show that this triangle is in the cliqueFinset of $G_ex$.
  simp [M_ex, G_ex];
  -- Since these are the only triangles in the graph, we can conclude that the set is a subset of the cliqueFinset.
  simp [Finset.subset_iff, SimpleGraph.cliqueFinset];
  simp +decide [ SimpleGraph.isNClique_iff ]

lemma M_ex_disjoint : IsEdgeDisjoint M_ex := by
  -- Since M_ex contains only one triangle, there are no edges to check for disjointness. Hence, M_ex is edge-disjoint.
  simp [IsEdgeDisjoint];
  -- Since $M_ex$ contains only one element, the pairwise disjointness condition is trivially satisfied.
  simp [Set.PairwiseDisjoint];
  decide +kernel

lemma M_ex_packing : IsTrianglePacking G_ex M_ex := by
  constructor;
  · -- Since $M_ex$ only contains the triangle $\{1, 2, 3\}$, we need to show that this triangle is in the cliqueFinset of $G_ex$.
    simp [M_ex, G_ex];
    -- Since these are the only triangles in the graph, we can conclude that the set is a subset of the cliqueFinset.
    simp [Finset.subset_iff, SimpleGraph.cliqueFinset];
    simp +decide [ SimpleGraph.isNClique_iff ];
  · -- Since M_ex contains only one triangle, there are no edges to check for disjointness. Hence, M_ex is edge-disjoint.
    simp [IsEdgeDisjoint];
    -- Since $M_ex$ contains only one element, the pairwise disjointness condition is trivially satisfied.
    simp [Set.PairwiseDisjoint];
    decide +kernel
lemma M_ex_card : M_ex.card = 2 := by
  native_decide +revert

lemma max_packing_le_2 : ∀ M, IsTrianglePacking G_ex M → M.card ≤ 2 := by
  rintro M ⟨ hM₁, hM₂ ⟩;
  have hM_card : M.card * 3 ≤ 10 := by
    have hM_card : M.card * 3 ≤ Finset.card (Finset.biUnion M triangleEdges) := by
      rw [ Finset.card_biUnion ];
      · rw [ Finset.sum_congr rfl fun x hx => show ( triangleEdges x ).card = 3 from ?_ ] ; aesop;
        have := hM₁ hx; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rcases this with ⟨ hx₁, hx₂ ⟩ ; fin_cases x <;> trivial;
      · exact hM₂;
    refine le_trans hM_card ?_;
    exact le_trans ( Finset.card_le_card ( Finset.biUnion_subset.mpr fun x hx => show triangleEdges x ⊆ Finset.image ( fun e : V_ex × V_ex => Sym2.mk ( e.1, e.2 ) ) ( Finset.offDiag ( Finset.univ : Finset V_ex ) ) from Finset.image_subset_iff.mpr fun e he => Finset.mem_image.mpr ⟨ e, Finset.mem_offDiag.mpr ⟨ Finset.mem_univ _, Finset.mem_univ _, by aesop ⟩, rfl ⟩ ) ) ( by decide );
  have : M.card ≤ 3 := Nat.le_of_lt_succ ( by linarith ) ; interval_cases _ : M.card <;> simp_all +decide ;
  -- Let's list out all possible triangles in $G_ex$ and check if we can find three edge-disjoint ones.
  have h_triangles : ∀ t ∈ M, t = {0, 1, 2} ∨ t = {0, 1, 3} ∨ t = {0, 1, 4} ∨ t = {0, 2, 3} ∨ t = {0, 2, 4} ∨ t = {0, 3, 4} ∨ t = {1, 2, 3} ∨ t = {1, 2, 4} ∨ t = {1, 3, 4} ∨ t = {2, 3, 4} := by
    intro t ht; specialize hM₁ ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    have : t.card = 3 := hM₁.card_eq; ( have : t ⊆ Finset.univ := Finset.subset_univ t; ( fin_cases t <;> trivial; ) );
  -- Let's list out all possible combinations of three triangles from the set of triangles in $G_ex$ and check if they are edge-disjoint.
  have h_combinations : ∀ t1 t2 t3 : Finset V_ex, t1 ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4} } : Finset (Finset V_ex)) → t2 ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4} } : Finset (Finset V_ex)) → t3 ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4} } : Finset (Finset V_ex)) → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 → ¬IsEdgeDisjoint {t1, t2, t3} := by
    unfold IsEdgeDisjoint;
    simp +decide [ Set.PairwiseDisjoint ];
    simp +decide [ Set.Pairwise ];
    intro t1 t2 t3 ht1 ht2 ht3 h1 h2 h3 h4 h5 h6 h7 h8; rcases ht1 with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> rcases ht2 with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> rcases ht3 with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> trivial;
  rcases Finset.card_eq_three.mp ‹_› with ⟨ t1, t2, t3, ht1, ht2, ht3 ⟩ ; simp_all +decide

lemma packing_num_eq_2 : packingNumber G_ex = 2 := by
  refine' le_antisymm _ _ <;> norm_num [ packingNumber ];
  · refine' csSup_le' _;
    rintro n ⟨ M, rfl, hM ⟩ ; exact max_packing_le_2 M hM;
  · refine' le_csSup _ _ <;> norm_num;
    · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
    · exact ⟨ M_ex, M_ex_card, M_ex_packing ⟩

lemma M_ex_isMax : IsMaxPacking G_ex M_ex := by
  -- Since $M_{ex}$ is a triangle packing and its cardinality is 2, and the maximum packing number is 2, $M_{ex}$ is a maximal packing.
  have h_max_packing : packingNumber G_ex = 2 := by
    refine' le_antisymm _ _ <;> norm_num [ packingNumber ];
    · refine' csSup_le' _;
      rintro n ⟨ M, rfl, hM ⟩ ; exact max_packing_le_2 M hM;
    · refine' le_csSup _ _ <;> norm_num;
      · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
      · exact ⟨ M_ex, M_ex_card, M_ex_packing ⟩;
  exact ⟨ M_ex_packing, h_max_packing ▸ M_ex_card ⟩

lemma no_small_cover : ∀ E : Finset (Sym2 V_ex), E.card < 3 → ¬(∀ t ∈ T_e G_ex e_ex, ¬Disjoint (triangleEdges t) E) := by
  intro E hE h_disjoint
  have h_card : E.card ≤ 2 := by
    grind;
  -- Let's consider the possible sets E with at most 2 edges and show that none of them can cover all triangles in T_e.
  have h_cases : ∀ E : Finset (Sym2 V_ex), E.card ≤ 2 → ∃ t ∈ T_e G_ex e_ex, Disjoint (triangleEdges t) E := by
    -- Let's list all possible sets E with at most 2 edges and check if any of them can cover all triangles in T_e.
    have h_cases : ∀ E : Finset (Sym2 V_ex), E.card ≤ 2 → ∃ t ∈ T_e G_ex e_ex, Disjoint (triangleEdges t) E := by
      intro E hE
      have h_triangles : T_e G_ex e_ex = { {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {1, 2, 3}, {1, 2, 4} } := by
        -- To prove equality of finite sets, we show each set is a subset of the other.
        apply Finset.ext
        intro t
        simp [T_e, G_ex, e_ex];
        native_decide +revert
      simp_all +decide [ Finset.subset_iff ];
      native_decide +revert;
    assumption;
  exact absurd ( h_cases E h_card ) ( by push_neg; tauto )

lemma Te_cover_ge_3 : coveringNumberOn G_ex (T_e G_ex e_ex) ≥ 3 := by
  -- By definition of coveringNumberOn, if there exists a set E with fewer than 3 edges that covers all triangles in T_e G_ex e_ex, then coveringNumberOn would be less than 3. However, we have already shown that no such E exists.
  have h_min : ∀ E : Finset (Sym2 V_ex), E.card < 3 → ¬(∀ t ∈ T_e G_ex e_ex, ¬Disjoint (triangleEdges t) E) := by
    -- Apply the lemma no_small_cover to conclude the proof.
    apply no_small_cover;
  -- By definition of coveringNumberOn, if there exists a set E with fewer than 3 edges that covers all triangles in T_e G_ex e_ex, then coveringNumberOn would be less than 3. However, we have already shown that no such E exists, so the infimum must be at least 3.
  apply le_csInf;
  · -- Let's choose any set E of edges that covers all triangles in T_e G_ex e_ex. For example, E = { (0, 1), (0, 2), (1, 2) }.
    use 3
    use {Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2)};
    -- Let's verify that the set { (0,1), (0,2), (1,2) } covers all triangles in T_e G_ex e_ex.
    simp [T_e, G_ex, e_ex];
    decide +revert;
  · exact fun n hn => not_lt.1 fun contra => h_min _ ( hn.choose_spec.1.symm ▸ contra ) hn.choose_spec.2

end AristotleLemmas

theorem tau_Te_counterexample :
    ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
      (e : Finset V) (he : e ∈ M),
    coveringNumberOn G (T_e G e) ≥ 3 := by
  simp +zetaDelta at *;
  use ULift ( Fin 5 );
  refine' ⟨ inferInstance, inferInstance, ⊤, inferInstance, _ ⟩;
  refine' ⟨ { { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ }, { ⟨ 0 ⟩, ⟨ 3 ⟩, ⟨ 4 ⟩ } }, _, _, _ ⟩ <;> norm_num;
  · decide +revert;
  · constructor;
    · constructor;
      · simp +decide [ Finset.subset_iff ];
      · intro x hx y hy hxy; simp_all +decide [ IsEdgeDisjoint ] ;
        rcases hx with ( rfl | rfl ) <;> rcases hy with ( rfl | rfl ) <;> simp +decide [ triangleEdges ] at hxy ⊢;
    · refine' le_antisymm _ _;
      · refine' le_csSup _ _;
        · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
        · use { {⟨0⟩, ⟨1⟩, ⟨2⟩}, {⟨0⟩, ⟨3⟩, ⟨4⟩} };
          unfold IsTrianglePacking;
          unfold IsEdgeDisjoint; simp +decide ;
          simp +decide [ Set.PairwiseDisjoint ];
          simp +decide [ Set.Pairwise ];
      · refine' csSup_le _ _ <;> norm_num;
        · exact ⟨ 0, ⟨ ∅, rfl, by unfold IsTrianglePacking; aesop_cat ⟩ ⟩;
        · rintro b x rfl hx; have := hx.1; simp_all +decide [ IsTrianglePacking ] ;
          -- Since $x$ is a subset of the set of all triangles in $K_5$, and $K_5$ has only 10 triangles, $x$ can have at most 2 elements.
          have h_card : x.card ≤ 2 := by
            have h_subset : x ⊆ Finset.image (fun t : Finset (Fin 5) => Finset.image (fun x : Fin 5 => ULift.up x) t) (Finset.powersetCard 3 (Finset.univ : Finset (Fin 5))) := by
              intro t ht; specialize this ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              simp_all +decide [ SimpleGraph.isNClique_iff ];
              rcases Finset.card_eq_three.mp this.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use { a.down, b.down, c.down } ; aesop;
            have h_card : ∀ s : Finset (Finset (Fin 5)), s ⊆ Finset.powersetCard 3 (Finset.univ : Finset (Fin 5)) → (∀ t ∈ s, ∀ u ∈ s, t ≠ u → Disjoint (Finset.image (fun x => Sym2.mk (x, x)) (Finset.offDiag t)) (Finset.image (fun x => Sym2.mk (x, x)) (Finset.offDiag u))) → s.card ≤ 2 := by
              native_decide +revert;
            contrapose! h_card;
            refine' ⟨ Finset.filter ( fun t => Finset.image ( fun x : Fin 5 => ULift.up x ) t ∈ x ) ( Finset.powersetCard 3 Finset.univ ), _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
            · intro t ht ht' u hu hu' htu; have := hx ht' hu'; simp_all +decide [ Finset.disjoint_left ] ;
              intro a x y hx hy hxy hx' z w hz hw hzw h; specialize this ( by
                simp_all +decide [ Finset.ext_iff ] ) ; simp_all +decide [ triangleEdges ] ;
              subst_vars; specialize this x y hx hy hxy; simp_all +decide [ Sym2.eq_swap ] ;
              exact s({ down := x }, { down := y });
              simp_all +decide [ Sym2.eq_swap ];
              exact this x y hz hw hxy |>.1 rfl rfl;
            · convert h_card using 1;
              refine' Finset.card_bij ( fun t ht => Finset.image ( fun x : Fin 5 => { down := x } ) t ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
              · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; rw [ Finset.image_injective ( fun x y hxy => by simpa using hxy ) |>.eq_iff ] at h; aesop;
              · exact fun b hb => by obtain ⟨ a, ha₁, ha₂ ⟩ := h_subset hb; exact ⟨ a, ⟨ ha₁, ha₂ ▸ hb ⟩, ha₂ ⟩ ;
          exact h_card;
  · refine' Or.inl ( le_csInf _ _ );
    · refine' ⟨ _, ⟨ Finset.univ, rfl, _ ⟩ ⟩;
      simp +decide [ Finset.disjoint_left ];
    · rintro n ⟨ E, rfl, hE ⟩;
      contrapose! hE;
      native_decide +revert

end