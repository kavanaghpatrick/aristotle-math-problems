/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2cc1e7bc-56ff-4751-9f36-98afd9713efd

The following was proved by Aristotle:

- theorem no_vertex_disjoint_packing_counterexample :
    ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    packingNumber G = 2 ∧
    ∀ M : Finset (Finset V), IsMaxPacking G M →
      ¬(∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f)
-/

/-
PESSIMIST: Hunt for counterexample to "vertex-disjoint packing always exists for ν=2"

The lemma `exists_good_packing_nu2` from file 2fe95b81 claims:
  For any graph with ν = 2, there exists a max packing where elements are vertex-disjoint.

We believe this is FALSE. This submission asks Aristotle to PROVE the negation:
  There exists a graph with ν = 2 where NO max packing has vertex-disjoint elements.

Expected counterexample: Graph with only triangles {1,2,3} and {1,4,5} sharing vertex 1.
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

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def vertexDisjoint (t1 t2 : Finset V) : Prop := Disjoint t1 t2

-- COUNTEREXAMPLE: Find a graph where no max packing has vertex-disjoint elements
noncomputable section AristotleLemmas

/-
K5 is the complete graph on 5 vertices.
-/
def K5 : SimpleGraph (Fin 5) := ⊤

lemma K5_edge_card : K5.edgeFinset.card = 10 := by
  simp +decide [ K5 ]

lemma card_triangleEdges_of_card_eq_3 {V : Type*} [Fintype V] [DecidableEq V] (t : Finset V) (h : t.card = 3) : (triangleEdges t).card = 3 := by
  obtain ⟨ x, y, z, hxyz ⟩ := Finset.card_eq_three.mp h;
  -- Since the off-diagonal pairs are (x,y), (x,z), and (y,z), and these are distinct, the image under Sym2.mk will have exactly 3 elements.
  have h_off_diag : Finset.offDiag {x, y, z} = {(x, y), (x, z), (y, x), (y, z), (z, x), (z, y)} := by
    aesop;
  unfold triangleEdges; aesop;

lemma card_edges_of_packing (M : Finset (Finset (Fin 5))) (h : IsTrianglePacking K5 M) :
    (M.biUnion triangleEdges).card = 3 * M.card := by
      have h_card : ∀ t ∈ M, (triangleEdges t).card = 3 := by
        -- Since $M$ is a triangle packing in $K5$, each element $t$ in $M$ is a 3-element subset of $Fin 5$.
        have h_card_t : ∀ t ∈ M, t.card = 3 := by
          exact fun t ht => by have := h.1 ht; exact (by
          exact Finset.mem_filter.mp this |>.2.2);
        exact?;
      rw [ Finset.card_biUnion, Finset.sum_congr rfl h_card, Finset.sum_const, smul_eq_mul, mul_comm ];
      exact h.2

lemma card_le_3_of_packing (M : Finset (Finset (Fin 5))) (h : IsTrianglePacking K5 M) :
    M.card ≤ 3 := by
      have h_card_edges : (M.biUnion triangleEdges).card = 3 * M.card := by
        exact?;
      have h_card_edges_le : (M.biUnion triangleEdges).card ≤ K5.edgeFinset.card := by
        refine Finset.card_le_card ?_;
        exact Finset.biUnion_subset.mpr fun x hx => Finset.image_subset_iff.mpr fun y hy => by have := h.1 hx; aesop;
      linarith [ show K5.edgeFinset.card = 10 by exact? ]

/-
The degree of a vertex v in a set of edges E is the number of edges in E that contain v.
-/
def degreeInEdges (E : Finset (Sym2 V)) (v : V) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

lemma degreeInEdges_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Finset (Sym2 V)) (v : V)
    (h : (s : Set ι).PairwiseDisjoint f) :
    degreeInEdges (s.biUnion f) v = ∑ i ∈ s, degreeInEdges (f i) v := by
      unfold degreeInEdges;
      rw [ Finset.card_filter ];
      rw [ Finset.sum_biUnion ];
      · simp +decide [ Finset.sum_ite ];
      · assumption

lemma degreeInEdges_triangle (t : Finset V) (ht : t.card = 3) (v : V) :
    degreeInEdges (triangleEdges t) v = if v ∈ t then 2 else 0 := by
      unfold degreeInEdges triangleEdges;
      split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ Finset.filter_image ];
      · rw [ Finset.card_eq_two ];
        have := Finset.card_eq_three.1 ht;
        rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all ( config := { decide := Bool.true } ) [ Finset.ext_iff, Sym2.eq_swap ] ;
        rcases ‹_› with ( rfl | rfl | rfl );
        · refine' ⟨ s(v, y), s(v, z), _, _ ⟩ <;> aesop;
        · refine' ⟨ Sym2.mk ( v, x ), Sym2.mk ( v, z ), _, _ ⟩ <;> aesop;
        · refine' ⟨ Sym2.mk ( v, x ), Sym2.mk ( v, y ), _, _ ⟩ <;> aesop;
          · exact ⟨ v, x, by aesop ⟩;
          · exact ⟨ y, v, by aesop ⟩;
      · aesop

lemma even_degree_of_triangle_packing (M : Finset (Finset V)) (h : IsEdgeDisjoint M)
    (h_card : ∀ t ∈ M, t.card = 3) (v : V) :
    Even (degreeInEdges (M.biUnion triangleEdges) v) := by
      -- Rewrite the degree of $v$ in $E_V$ using the previous results.
      rw [degreeInEdges_biUnion M triangleEdges v h];
      -- By `degreeInEdges_triangle`, each term in the sum is 0 or 2.
      have h_even_terms : ∀ t ∈ M, degreeInEdges (triangleEdges t) v = if v ∈ t then 2 else 0 := by
        exact?;
      exact even_iff_two_dvd.mpr ( Finset.dvd_sum fun t ht => by rw [ h_even_terms t ht ] ; split_ifs <;> norm_num )

lemma degreeInEdges_K5 (v : Fin 5) : degreeInEdges K5.edgeFinset v = 4 := by
  fin_cases v <;> simp +decide [ K5, SimpleGraph.edgeFinset ]

lemma degreeInEdges_diff (A B : Finset (Sym2 V)) (h : B ⊆ A) (v : V) :
    degreeInEdges (A \ B) v = degreeInEdges A v - degreeInEdges B v := by
      rw [ eq_tsub_iff_add_eq_of_le ];
      · unfold degreeInEdges;
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with e ; by_cases he : e ∈ B <;> aesop;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx₁ |>.1 ) |>.2 ( Finset.mem_filter.mp hx₂ |>.1 );
      · exact Finset.card_le_card fun x hx => by aesop;

lemma no_packing_size_3 : ¬ ∃ M : Finset (Finset (Fin 5)), M.card = 3 ∧ IsTrianglePacking K5 M := by
  simp +decide [ IsTrianglePacking ];
  unfold IsEdgeDisjoint; simp +decide [ Finset.subset_iff ] ;
  intros x hx hclique hdisjoint;
  -- Let's list all possible triangle edges and show that there cannot be three edge-disjoint triangles in $K_5$.
  have h_all_triangles : ∀ t ∈ x, t ∈ Finset.filter (fun t => t.card = 3) (Finset.powerset (Finset.univ : Finset (Fin 5))) := by
    simp_all +decide [ SimpleGraph.isNClique_iff ];
  -- Let's list all possible triangle edges and show that there cannot be three edge-disjoint triangles in $K_5$. We will check all combinations.
  have h_combinations : ∀ y : Finset (Finset (Fin 5)), y ⊆ Finset.filter (fun t => t.card = 3) (Finset.powerset (Finset.univ : Finset (Fin 5))) → y.card = 3 → ¬(Finset.card (Finset.biUnion y triangleEdges) = 3 * 3) := by
    native_decide;
  exact h_combinations x h_all_triangles hx ( by rw [ card_edges_of_packing x ⟨ by aesop_cat, hdisjoint ⟩ ] ; simp +decide [ hx ] )

lemma exists_packing_size_2 : ∃ M : Finset (Finset (Fin 5)), M.card = 2 ∧ IsTrianglePacking K5 M := by
  -- Consider the set M = {{0, 1, 2}, {0, 3, 4}}.
  use { {0, 1, 2}, {0, 3, 4} };
  unfold IsTrianglePacking; simp +decide ;
  unfold IsEdgeDisjoint; simp +decide [ Set.PairwiseDisjoint ] ;
  simp +decide [ Finset.insert_subset_iff, K5 ]

lemma packingNumber_K5 : packingNumber K5 = 2 := by
  unfold packingNumber;
  rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
  · exact ⟨ 0, ⟨ ∅, rfl, by unfold IsTrianglePacking; aesop_cat ⟩ ⟩;
  · rintro n ⟨ M, rfl, hM ⟩ ; exact le_of_not_gt fun h => by have := card_le_3_of_packing M hM; interval_cases _ : M.card ; exact no_packing_size_3 <| by tauto;
  · exact fun w hw => ⟨ 2, by obtain ⟨ M, hM₁, hM₂ ⟩ := exists_packing_size_2; exact ⟨ M, hM₁, hM₂ ⟩, hw ⟩

lemma triangles_not_disjoint_in_K5 (t1 t2 : Finset (Fin 5)) (h1 : t1.card = 3) (h2 : t2.card = 3) : ¬ Disjoint t1 t2 := by
  native_decide +revert

lemma not_vertex_disjoint_packing_K5 (M : Finset (Finset (Fin 5))) (h_packing : IsTrianglePacking K5 M) (h_card : M.card = 2) : ¬ (∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f) := by
  rw [ Finset.card_eq_two ] at h_card ; aesop;
  · unfold vertexDisjoint at a; have := h_packing.1; simp_all +decide [ Finset.subset_iff ] ;
    exact absurd ( triangles_not_disjoint_in_K5 x w_1 ( by simpa using this.1.2 ) ( by simpa using this.2.2 ) ) ( by aesop );
  · unfold IsTrianglePacking at h_packing;
    simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ];
    exact absurd ( Finset.card_le_univ ( x ∪ w ) ) ( by rw [ Finset.card_union_of_disjoint a ] ; exact not_le_of_gt ( by { have := h_packing.1.1.2; have := h_packing.1.2.2; aesop_cat } ) )

lemma K5_counterexample : packingNumber K5 = 2 ∧
    ∀ M : Finset (Finset (Fin 5)), IsMaxPacking K5 M →
      ¬(∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f) := by
        refine ⟨ packingNumber_K5, ?_ ⟩;
        intro M hM h
        obtain ⟨M_card, hM_card⟩ := hM
        have h_card : M.card = 2 := by
          exact hM_card.trans ( packingNumber_K5 );
        exact not_vertex_disjoint_packing_K5 M M_card h_card h

end AristotleLemmas

theorem no_vertex_disjoint_packing_counterexample :
    ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    packingNumber G = 2 ∧
    ∀ M : Finset (Finset V), IsMaxPacking G M →
      ¬(∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f) := by
  by_contra! h_contra;
  -- Let's choose any finite type `V` and define the graph `G` as `K5`.
  set V : Type := Fin 5;
  specialize h_contra ( ULift V );
  obtain ⟨ M, hM₁, hM₂ ⟩ := h_contra ( by infer_instance ) ( by infer_instance ) ( SimpleGraph.comap ( fun x : ULift V => x.down ) K5 ) ( by infer_instance ) ( by
    convert packingNumber_K5 using 1;
    unfold packingNumber;
    congr! 3;
    constructor <;> rintro ⟨ M, hM₁, hM₂ ⟩;
    · use M.image (fun t => t.image (fun x => x.down));
      rw [ Finset.card_image_of_injOn ];
      · refine' ⟨ hM₁, _, _ ⟩;
        · intro t ht;
          obtain ⟨ t', ht', rfl ⟩ := Finset.mem_image.mp ht;
          have := hM₂.1 ht';
          simp_all +decide [ SimpleGraph.isNClique_iff ];
          simp_all +decide [ SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective ];
          intro x hx y hy hxy; obtain ⟨ u, hu, rfl ⟩ := hx; obtain ⟨ v, hv, rfl ⟩ := hy; aesop;
        · intro t₁ ht₁ t₂ ht₂ hne; obtain ⟨ t₁', ht₁', rfl ⟩ := Finset.mem_image.mp ht₁; obtain ⟨ t₂', ht₂', rfl ⟩ := Finset.mem_image.mp ht₂; simp_all +decide [ IsEdgeDisjoint ] ;
          have := hM₂.2 ht₁' ht₂';
          simp_all +decide [ Finset.disjoint_left, Function.onFun ];
          intro a ha₁ ha₂; specialize this ( by aesop ) ; simp_all +decide [ triangleEdges ] ;
          rcases ha₁ with ⟨ a₁, b₁, ⟨ ha₁, hb₁, hab₁ ⟩, rfl ⟩ ; rcases ha₂ with ⟨ a₂, b₂, ⟨ ha₂, hb₂, hab₂ ⟩, h ⟩ ; specialize this a₁ b₁ ha₁ hb₁ hab₁ rfl a₂ b₂ ha₂ hb₂ hab₂ ; simp_all +decide [ Sym2.eq_swap ] ;
      · intro t ht t' ht' h; ext x; replace h := Finset.ext_iff.mp h ( x.down ) ; aesop;
    · use M.image (fun t => t.image (fun x => ULift.up x));
      rw [ Finset.card_image_of_injective ];
      · refine' ⟨ hM₁, _, _ ⟩;
        · intro t ht;
          rw [ Finset.mem_image ] at ht; obtain ⟨ t', ht', rfl ⟩ := ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          have := hM₂.1 ht'; simp_all +decide [ SimpleGraph.isClique_iff, Finset.card_image_of_injective, Function.Injective ] ;
          simp_all +decide [ SimpleGraph.isNClique_iff, Set.Pairwise ];
        · intro t ht u hu htu;
          simp +zetaDelta at *;
          obtain ⟨ x, hx₁, rfl ⟩ := ht; obtain ⟨ y, hy₁, rfl ⟩ := hu; have := hM₂.2 hx₁ hy₁; simp_all +decide [ Finset.disjoint_left ] ;
          intro a ha hb; specialize this ( by aesop ) ; simp_all +decide [ triangleEdges ] ;
          rcases ha with ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩ ; rcases hb with ⟨ c, d, ⟨ hc, hd, hcd ⟩, h ⟩ ; specialize this a b ha hb hab rfl c d hc hd hcd ; aesop;
      · intro t₁ t₂ h; ext x; replace h := Finset.ext_iff.mp h ( ULift.up x ) ; aesop; );
  obtain ⟨ e, he₁, he₂ ⟩ := hM₂;
  obtain ⟨ f, hf₁, hf₂ ⟩ := Finset.exists_mem_ne ( show 1 < Finset.card M from by
                                                    have := hM₁.2;
                                                    rw [ this ];
                                                    refine' lt_of_lt_of_le _ ( le_csSup _ <| show 2 ∈ _ from _ );
                                                    · decide +revert;
                                                    · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
                                                    · simp +decide [ IsTrianglePacking ];
                                                      simp +decide [ IsEdgeDisjoint ];
                                                      simp +decide [ SimpleGraph.cliqueFinset ];
                                                      simp +decide [ SimpleGraph.isNClique_iff ];
                                                      simp +decide [ SimpleGraph.IsClique ];
                                                      simp +decide [ Set.Pairwise ];
                                                      simp +decide [ K5 ];
                                                      simp +decide [ Finset.subset_iff, Finset.mem_powersetCard ];
                                                      simp +decide [ Set.PairwiseDisjoint ];
                                                      exists { { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ }, { ⟨ 0 ⟩, ⟨ 3 ⟩, ⟨ 4 ⟩ } } ) e;
  have := hM₁.1.1 he₁; have := hM₁.1.1 hf₁; simp_all +decide [ Finset.card_eq_three ] ;
  simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_eq_three ];
  simp_all +decide [ SimpleGraph.IsClique, SimpleGraph.comap ];
  obtain ⟨ x, y, hxy, z, hxz, hyz, rfl ⟩ := this.2; obtain ⟨ u, v, huv, w, huw, hvw, rfl ⟩ := ‹ ( ( e : Set ( ULift V ) ).Pairwise fun u v => K5.Adj u.down v.down ) ∧ _›.2; simp_all +decide [ Finset.disjoint_left ] ;
  specialize he₂ _ hf₁ ; simp_all +decide [ vertexDisjoint ];
  have h_card : Finset.card ({x, y, z, u, v, w} : Finset V) = 6 := by
    simp +decide [ *, Finset.card_insert_of_notMem ];
  exact h_card.not_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by decide ) )

end