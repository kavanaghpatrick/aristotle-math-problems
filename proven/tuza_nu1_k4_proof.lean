/-
TUZA'S CONJECTURE - ν=1 CASE: PROVED via K₄ Structure Argument

This file contains Aristotle-verified proofs for Tuza's conjecture when ν(G) = 1.
Submission UUID: 16d696d6-363c-4f8a-b1b7-76dab6ffe349

KEY RESULTS:
- tuza_case_nu_1: If ν(G) = 1 then τ(G) ≤ 2
- extension_triangle_exists: If ν=1 and τ>2, any edge in a triangle extends to another triangle
- exists_K4_of_nu1_tau_gt2: If ν=1 and τ>2, graph contains K₄
- K4_cover_le_2: K₄ can be covered by 2 opposite edges

PROOF OUTLINE:
1. Assume ν=1 and τ>2 (contradiction target)
2. For any triangle T and edge e in T, find another triangle T' sharing exactly e
3. This extension property forces a K₄ structure
4. But K₄ can be covered by 2 opposite edges, so τ≤2 - contradiction!

This is a novel formalization of the ν=1 case using K₄ structure analysis.
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-! ## Core Definitions -/

def triangleEdges {V : Type} [DecidableEq V] (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint {V : Type} [DecidableEq V] (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

noncomputable def trianglePackingNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

noncomputable def triangleCoveringNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

/-! ## Foundational Lemmas -/

lemma tuza_base_case {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h;
    refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ( Classical.choose_spec ( Finset.card_pos.mp ( Nat.pos_of_ne_zero h ) ) ) ), _ ⟩ ) ) ) <;> norm_num;
    intro x hx y hy; aesop;
  unfold triangleCoveringNumber;
  unfold IsTriangleCovering; aesop;
  rw [ show ( Finset.image Finset.card ( Finset.filter ( fun S : Finset ( Sym2 V ) => ( G.deleteEdges ( S : Set ( Sym2 V ) ) ).CliqueFree 3 ) ( G.edgeFinset.powerset ) ) ).min = some 0 from ?_ ];
  · rfl;
  · refine' le_antisymm _ _;
    · refine' Finset.min_le _ ; aesop;
    · simp +decide [ Finset.min ];
      exact fun _ _ _ => WithTop.coe_le_coe.mpr ( Nat.zero_le _ )

lemma triangleCoveringNumber_le_card_add_deleteEdges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧ IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop;
    have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering ( G.deleteEdges ( S : Set ( Sym2 V ) ) ) ) ( G.deleteEdges ( S : Set ( Sym2 V ) ) |> SimpleGraph.edgeFinset |> Finset.powerset ) ) ) from ?_ ) ; aesop;
    · have := Finset.mem_of_min h; aesop;
    · simp +zetaDelta at *;
      use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering];
  have h_union : IsTriangleCovering G (S ∪ T) := by
    unfold IsTriangleCovering at *; aesop;
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber;
    have h_union_card : (S ∪ T).card ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [ Finset.subset_iff, SimpleGraph.deleteEdges ];
      exact ⟨ S ∪ T, ⟨ fun x hx => by aesop, h_union ⟩, rfl ⟩;
    have := Finset.min_le h_union_card; aesop;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
  exact h_union_card.trans ( Finset.card_union_le _ _ ) |> le_trans <| by rw [ hT.2.2 ] ;

lemma exists_max_packing {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_exists_packing : ∃ P : Finset (Finset V), P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
    have h_finite : (G.cliqueFinset 3).powerset.Nonempty := by
      exact ⟨ ∅, Finset.mem_powerset.mpr <| Finset.empty_subset _ ⟩
    have h_exists_packing : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧ ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card := by
      exact Finset.exists_max_image _ _ ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide [ IsEdgeDisjoint ] ⟩ ⟩;
    obtain ⟨ P, hP₁, hP₂ ⟩ := h_exists_packing; use P; aesop;
    exact le_antisymm ( Finset.le_sup ( f := Finset.card ) ( by aesop ) ) ( Finset.sup_le fun Q hQ => by aesop );
  exact h_exists_packing

lemma packing_one_implies_intersect {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  contrapose! h;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨ h1, Finset.singleton_subset_iff.mpr h2 ⟩, _ ⟩ ) );
  · rw [ Finset.card_pair ] ; aesop;
    unfold triangleEdges at h; aesop;
    simp_all +decide [ Finset.ext_iff ];
    have := Finset.card_eq_three.mp h2.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; specialize h a b; aesop;
  · intro x hx y hy hxy; aesop;
    exact h.symm

/-! ## K₄ Structure Lemmas (PROVED BY ARISTOTLE) -/

/--
If the triangle packing number is 1 and the triangle covering number is greater than 2,
then for any triangle T and any edge e in T, there exists another triangle T' that shares
exactly the edge e with T.
-/
lemma extension_triangle_exists {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 1) (htau : triangleCoveringNumber G > 2)
    (T : Finset V) (hT : G.IsNClique 3 T)
    (e : Sym2 V) (he : e ∈ triangleEdges T) :
    ∃ T', G.IsNClique 3 T' ∧ triangleEdges T ∩ triangleEdges T' = {e} := by
      -- Let $S = \text{triangleEdges}(T) \setminus \{e\}$. Since $T$ is a triangle, $|S| = 2$.
      set S : Finset (Sym2 V) := (triangleEdges T).erase e
      have hS_card : S.card = 2 := by
        rw [ Finset.card_erase_of_mem he ];
        unfold triangleEdges;
        have := Finset.card_eq_three.mp hT.2; aesop;
        simp +decide [ *, Finset.card ];
        simp +decide [ *, Finset.offDiag ];
        simp +decide [ *, Multiset.filter_cons, Multiset.filter_singleton ];
        split_ifs <;> simp_all +decide [ Sym2.eq_swap ];
      -- Since $\tau(G) > 2$, $S$ is not a triangle covering.
      have hS_not_covering : ¬IsTriangleCovering G S := by
        contrapose! htau;
        refine' le_trans ( triangleCoveringNumber_le_card_add_deleteEdges G S _ ) _;
        · intro x hx; aesop;
          unfold triangleEdges at right; aesop;
          exact hT.1 left_1 left_2 right_1;
        · rw [ show triangleCoveringNumber ( G.deleteEdges ( S : Set ( Sym2 V ) ) ) = 0 from _ ] ; aesop;
          convert tuza_base_case _ _;
          unfold IsTriangleCovering at htau; aesop;
          unfold trianglePackingNumber; aesop;
          exact Finset.eq_empty_of_forall_notMem fun x hx => htau x <| by have := a hx; aesop;
      -- So there exists a triangle $T'$ in $G \setminus S$.
      obtain ⟨T', hT'⟩ : ∃ T' : Finset V, G.IsNClique 3 T' ∧ ∀ f ∈ S, ¬f ∈ triangleEdges T' := by
        obtain ⟨ T', hT' ⟩ := Finset.nonempty_of_ne_empty hS_not_covering; use T'; aesop;
        · exact hT'.mono ( by aesop_cat );
        · rcases Finset.mem_image.mp a_2 with ⟨ x, hx, rfl ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ];
          have := hT'.1 hx.1 hx.2.1 hx.2.2; simp_all +decide [ SimpleGraph.adj_comm ] ;
      -- Since $T$ and $T'$ are triangles, they must share an edge. Let's denote this edge as $e'$.
      obtain ⟨e', he'⟩ : ∃ e' ∈ triangleEdges T, e' ∈ triangleEdges T' := by
        have h_intersect : ¬Disjoint (triangleEdges T) (triangleEdges T') := by
          bound;
          exact absurd ( packing_one_implies_intersect G hnu T T' ( by simpa using hT ) ( by simpa using left ) ) ( by aesop );
        exact Finset.not_disjoint_iff.mp h_intersect;
      grind

/--
If the triangle packing number is 1 and the triangle covering number is greater than 2,
then the graph contains a K4 clique.
-/
lemma exists_K4_of_nu1_tau_gt2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 1) (htau : triangleCoveringNumber G > 2) :
    ∃ s, G.IsNClique 4 s := by
      -- Let $T_0 = \{u, v, w\}$ be a triangle.
      obtain ⟨T, hT_clique, hT_card⟩ : ∃ T : Finset V, G.IsNClique 3 T := by
        contrapose! hnu;
        unfold trianglePackingNumber; aesop;
        rw [ show G.cliqueFinset 3 = ∅ by ext; aesop ] at a ; aesop;
        rw [ Finset.filter_singleton ] at a ; aesop;
      -- Let $e_1 = \{u, v\}$, $e_2 = \{v, w\}$, and $e_3 = \{w, u\}$.
      obtain ⟨u, v, w, huv, hvw, hwu⟩ : ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧ T = {u, v, w} := by
        rcases Finset.card_eq_three.mp hT_card with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v, w ; aesop;
        exact right.symm;
      -- By `extension_triangle_exists`, there exists $T_3 = \{w, u, z\}$ for some $z \notin T_0$.
      obtain ⟨z, hz⟩ : ∃ z : V, z ∉ ({u, v, w} : Finset V) ∧ G.Adj w z ∧ G.Adj u z := by
        -- By `extension_triangle_exists`, there exists $T_3 = \{w, u, z\}$ for some $z \notin T_0$ sharing exactly the edge $\{w, u\}$ with $T_0$.
        have hT3 : ∃ T3 : Finset V, G.IsNClique 3 T3 ∧ triangleEdges ({u, v, w} : Finset V) ∩ triangleEdges T3 = {Sym2.mk (w, u)} := by
          apply extension_triangle_exists G hnu htau {u, v, w};
          · aesop;
            constructor <;> aesop;
          · unfold triangleEdges; aesop;
            exact ⟨ w, u, by aesop ⟩;
        obtain ⟨ T3, hT3_clique, hT3_edge ⟩ := hT3;
        -- Since $T3$ is a triangle and shares exactly the edge $\{w, u\}$ with $T0$, $T3$ must contain $w$ and $u$.
        have hT3_contains_wu : w ∈ T3 ∧ u ∈ T3 := by
          replace hT3_edge := Finset.ext_iff.mp hT3_edge ( Sym2.mk ( w, u ) ) ; aesop;
          · unfold triangleEdges at right_1; aesop;
          · unfold triangleEdges at right_1; aesop;
        -- Since $T3$ is a triangle and contains $w$ and $u$, it must also contain a third vertex $z$.
        obtain ⟨z, hz⟩ : ∃ z : V, z ∈ T3 ∧ z ≠ w ∧ z ≠ u := by
          have := Finset.card_eq_three.mp hT3_clique.2; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; use if x = w then if y = u then z else y else if y = w then if x = u then z else x else if z = w then if x = u then y else x else w; aesop;
        use z;
        bound;
        · simp_all +decide [ SimpleGraph.IsNClique ];
          replace hT3_edge := Finset.ext_iff.mp hT3_edge ( Sym2.mk ( v, w ) ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
          contrapose! hT3_edge; simp_all +decide [ triangleEdges ] ;
          exact ⟨ ⟨ v, w, by aesop ⟩, ⟨ v, w, by aesop ⟩ ⟩;
        · have := hT3_clique.1 left_1 left_2; aesop;
        · have := hT3_clique.1; aesop;
      -- By `extension_triangle_exists`, there exists $T_1 = \{u, v, x\}$ for some $x \notin T_0$.
      obtain ⟨x, hx⟩ : ∃ x : V, x ∉ ({u, v, w} : Finset V) ∧ G.Adj u x ∧ G.Adj v x := by
        have := extension_triangle_exists G hnu htau { u, v, w } ?_ ( Sym2.mk ( u, v ) ) ?_ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · obtain ⟨ T', ⟨ hT'_clique, hT'_card ⟩, hT'_edge ⟩ := this;
          -- Since $T'$ is a triangle and shares exactly the edge $\{u, v\}$ with $T$, it must contain $u$ and $v$.
          have hT'_contains_uv : u ∈ T' ∧ v ∈ T' := by
            simp_all +decide [ Finset.eq_singleton_iff_unique_mem, triangleEdges ];
            grind;
          -- Since $T'$ is a triangle and contains $u$ and $v$, it must also contain a third vertex $x$.
          obtain ⟨x, hx⟩ : ∃ x : V, x ∈ T' ∧ x ≠ u ∧ x ≠ v := by
            exact Exists.imp ( by aesop ) ( Finset.exists_ne_of_one_lt_card ( show 1 < Finset.card ( Finset.erase T' u ) from by rw [ Finset.card_erase_of_mem hT'_contains_uv.1, hT'_card ] ; decide ) v );
          use x;
          simp_all +decide [ Finset.ext_iff, triangleEdges ];
          have := hT'_edge ( Sym2.mk ( u, x ) ) ; have := hT'_edge ( Sym2.mk ( v, x ) ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
          bound;
          · specialize this_1 u x ; simp_all +decide;
            grind;
          · exact hT'_clique ( by aesop ) ( by aesop ) ( by aesop );
          · exact hT'_clique ( by aesop ) ( by aesop ) ( by aesop );
        · exact Finset.mem_image.mpr ⟨ ( u, v ), by aesop_cat ⟩;
      -- By `extension_triangle_exists`, there exists $T_2 = \{v, w, y\}$ for some $y \notin T_0$.
      obtain ⟨y, hy⟩ : ∃ y : V, y ∉ ({u, v, w} : Finset V) ∧ G.Adj v y ∧ G.Adj w y := by
        have := extension_triangle_exists G hnu htau { u, v, w } ?_ ( Sym2.mk ( v, w ) ) ?_ <;> simp_all +decide [ SimpleGraph.IsNClique ];
        · obtain ⟨ T', hT'_clique, hT'_edge ⟩ := this;
          -- Since $T'$ is a triangle and shares exactly the edge $(v, w)$ with $T$, it must contain $v$ and $w$.
          have hT'_contains_vw : v ∈ T' ∧ w ∈ T' := by
            simp_all +decide [ Finset.eq_singleton_iff_unique_mem, triangleEdges ];
            grind;
          -- Since $T'$ is a triangle and shares exactly the edge $(v, w)$ with $T$, it must contain exactly one more vertex $y$.
          obtain ⟨y, hy⟩ : ∃ y : V, y ∈ T' ∧ y ≠ v ∧ y ≠ w := by
            have := Finset.card_eq_three.mp hT'_clique.2; obtain ⟨ a, b, c, ha, hb, hc, habc ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
            grind;
          use y;
          bound;
          · simp_all +decide [ Finset.eq_singleton_iff_unique_mem, triangleEdges ];
            contrapose! hT'_edge;
            rintro -;
            use Sym2.mk ( y, v ), y, v ; aesop;
          · have := hT'_clique.1; simp_all +decide [ SimpleGraph.isClique_iff, Finset.subset_iff ] ;
            exact this left_3 left_4 ( by aesop );
          · have := hT'_clique.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact this right_3 left_4 ( by aesop );
        · constructor <;> aesop;
        · exact Finset.mem_image.mpr ⟨ ( v, w ), by aesop ⟩;
      -- Since $\nu=1$, $T_1$ and $T_2$ must share an edge.
      have h_share_edge : x = y := by
        have h_share_edge : ¬ Disjoint (triangleEdges {u, v, x}) (triangleEdges {v, w, y}) := by
          apply packing_one_implies_intersect G hnu;
          · simp_all +decide [ SimpleGraph.cliqueFinset ];
            simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
          · simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
        unfold triangleEdges at h_share_edge; simp_all +decide [ Finset.disjoint_left ] ;
        simp_all +decide [ Sym2.eq_iff, eq_comm ];
        simp_all +decide [ Sym2.eq_swap ];
        aesop;
      -- By `extension_triangle_exists`, there exists $T_3 = \{w, u, z\}$ for some $z \notin T_0$.
      have hz_eq_x : z = x := by
        have hz_eq_x : ¬ Disjoint (triangleEdges ({w, u, z} : Finset V)) (triangleEdges ({u, v, x} : Finset V)) := by
          apply packing_one_implies_intersect G hnu;
          · simp_all +decide [ SimpleGraph.cliqueFinset ];
            simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton ] <;> aesop;
          · simp_all +decide [ SimpleGraph.cliqueFinset ];
            simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
        contrapose! hz_eq_x;
        simp_all +decide [ Finset.disjoint_left, triangleEdges ];
        intros; subst_vars; simp_all +decide [ Sym2.eq_iff ] ;
        grind;
      use {u, v, w, x};
      simp_all +decide [ SimpleGraph.isNClique_iff ];
      rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop

/--
If a graph has triangle packing number 1 and contains a K4 clique, then its triangle
covering number is at most 2.
-/
lemma K4_cover_le_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 1) (s : Finset V) (hs : G.IsNClique 4 s) :
    triangleCoveringNumber G ≤ 2 := by
      -- Let $S = \{(a, b), (c, d)\}$.
      obtain ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, hs⟩ : ∃ t1 t2 t3 t4 : V, t1 ∈ s ∧ t2 ∈ s ∧ t3 ∈ s ∧ t4 ∈ s ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t1 ≠ t4 ∧ t2 ≠ t3 ∧ t2 ≠ t4 ∧ t3 ≠ t4 ∧ G.Adj t1 t2 ∧ G.Adj t1 t3 ∧ G.Adj t1 t4 ∧ G.Adj t2 t3 ∧ G.Adj t2 t4 ∧ G.Adj t3 t4 := by
        rcases Finset.card_eq_succ.mp hs.2 with ⟨ t, ht ⟩;
        rcases ht with ⟨ u, hu, rfl, hu' ⟩ ; rcases Finset.card_eq_three.mp hu' with ⟨ v, w, x, hv, hw, hx, h ⟩ ; use t, v, w, x; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have hS : ∀ T : Finset V, G.IsNClique 3 T → (triangleEdges T ∩ {Sym2.mk (t1, t2), Sym2.mk (t3, t4)}).Nonempty := by
        intros T hT;
        have h_inter : ¬ Disjoint (triangleEdges T) (triangleEdges {t1, t2, t3}) ∧ ¬ Disjoint (triangleEdges T) (triangleEdges {t1, t2, t4}) ∧ ¬ Disjoint (triangleEdges T) (triangleEdges {t1, t3, t4}) ∧ ¬ Disjoint (triangleEdges T) (triangleEdges {t2, t3, t4}) := by
          bound;
          · have := packing_one_implies_intersect G hnu T { t1, t2, t3 } ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          · have := packing_one_implies_intersect G hnu T { t1, t2, t4 } ; simp_all +decide [ Finset.disjoint_left ] ;
            contrapose! this; simp_all +decide [ SimpleGraph.IsNClique ] ;
            constructor <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          · have := packing_one_implies_intersect G hnu T { t1, t3, t4 } ?_ ?_ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          · have := packing_one_implies_intersect G hnu T { t2, t3, t4 } ; simp_all +decide [ Finset.disjoint_left ];
            contrapose! this; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        simp_all +decide [ Finset.disjoint_left, Finset.mem_inter ];
        unfold triangleEdges at *; simp_all +decide [ Finset.Nonempty ] ;
        rcases h_inter with ⟨ ⟨ x, ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩, ⟨ c, d, ⟨ hc, hd, hcd ⟩, hx ⟩ ⟩, ⟨ y, ⟨ a', b', ⟨ ha', hb', hab' ⟩, rfl ⟩, ⟨ c', d', ⟨ hc', hd', hcd' ⟩, hy ⟩ ⟩, ⟨ z, ⟨ a'', b'', ⟨ ha'', hb'', hab'' ⟩, rfl ⟩, ⟨ c'', d'', ⟨ hc'', hd'', hcd'' ⟩, hz ⟩ ⟩, ⟨ w, ⟨ a''', b''', ⟨ ha''', hb''', hab''' ⟩, rfl ⟩, ⟨ c''', d''', ⟨ hc''', hd''', hcd''' ⟩, hw ⟩ ⟩ ⟩;
        simp_all +decide [ Sym2.eq_iff ];
        grind;
      have hS_cover : IsTriangleCovering G {Sym2.mk (t1, t2), Sym2.mk (t3, t4)} := by
        unfold IsTriangleCovering; aesop;
        intro T hT; specialize hS T; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        contrapose! hS;
        unfold triangleEdges; aesop;
        · intro x hx y hy hxy; have := left_12 hx hy; aesop;
        · simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
          intro a x y hx hy hxy ha; have := left_12 hx hy; simp_all +decide [ SimpleGraph.deleteEdges ] ;
      unfold triangleCoveringNumber;
      have h_min_le_two : 2 ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
        simp +zetaDelta at *;
        refine' ⟨ { s(t1, t2), s(t3, t4) }, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
      have := Finset.min_le h_min_le_two; aesop;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop

/-! ## MAIN THEOREM -/

/--
MAIN THEOREM: When ν(G) = 1, we have τ(G) ≤ 2

This is proved by contradiction:
1. Assume τ > 2
2. Use extension_triangle_exists repeatedly to show extensions force K₄
3. exists_K4_of_nu1_tau_gt2 gives us the K₄
4. K4_cover_le_2 shows K₄ implies τ ≤ 2, contradiction!
-/
theorem tuza_case_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  by_contra h_contra;
  obtain ⟨s, hs⟩ : ∃ s : Finset V, G.IsNClique 4 s := by
    apply exists_K4_of_nu1_tau_gt2 G h (by linarith);
  exact h_contra <| K4_cover_le_2 G h s hs

end
