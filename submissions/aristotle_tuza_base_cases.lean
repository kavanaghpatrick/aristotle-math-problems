/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8642a30e-767a-4974-b2c9-f849f173a4fc

The following was proved by Aristotle:

- theorem tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0

- theorem tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2
-/

/-
Tuza's Conjecture for ν ≤ 3: Case-by-Case Approach
Prove each case (ν=0,1,2,3) individually, then combine.
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

-- Case ν = 0: No triangles, so τ = 0
theorem tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  -- If the triangle packing number is zero, then there are no triangles in the graph.
  have h_no_triangles : ∀ t : Finset V, t ∈ G.cliqueFinset 3 → False := by
    contrapose! h; aesop;
    unfold trianglePackingNumber at a;
    simp_all +decide [ Finset.max ];
    -- Since $w$ is a triangle, the set $\{w\}$ is a valid triangle packing.
    have h_packing : isTrianglePacking G {w} := by
      constructor <;> aesop;
    -- Since $\{w\}$ is a valid triangle packing, its size is at least 1.
    have h_size : (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset).sup (WithBot.some ∘ Finset.card) ≥ 1 := by
      exact le_trans ( by aesop ) ( Finset.le_sup ( f := WithBot.some ∘ Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ( by aesop ) ), h_packing ⟩ ) );
    cases h : Finset.sup ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ( WithBot.some ∘ Finset.card ) <;> aesop;
  unfold triangleCoveringNumber;
  rw [ Finset.min_eq_inf_withTop ];
  rw [ Finset.inf_eq_bot_iff.mpr ] <;> aesop;
  constructor <;> aesop

-- Case ν = 1: Single packing triangle, τ ≤ 2
-- All triangles share a vertex with the packing triangle
-- They form an intersecting family → star or K4 → τ ≤ 2
noncomputable section AristotleLemmas

/-
If a triangle T intersects three triangles forming a K4 (minus one face) in at least 2 vertices each, then T is contained in the K4 vertices.
-/
lemma K4_intersecting {u v w z : V} (h_distinct : ({u, v, w, z} : Finset V).card = 4)
    (T : Finset V) (hT : T.card = 3)
    (h1 : ({u, v, w} ∩ T).card ≥ 2)
    (h2 : ({u, v, z} ∩ T).card ≥ 2)
    (h3 : ({u, w, z} ∩ T).card ≥ 2) :
    T ⊆ {u, v, w, z} := by
      -- Suppose there exists an element $x \in T$ such that $x \notin \{u, v, w, z\}$.
      by_contra h_contra
      obtain ⟨x, hxT, hxS⟩ : ∃ x ∈ T, x ∉ ({u, v, w, z} : Finset V) := by
        exact Finset.not_subset.mp h_contra;
      -- Since $|T| = 3$ and $x \notin \{u, v, w, z\}$, it follows that $T \cap \{u, v, w, z\}$ contains at most two vertices.
      have h_inter : (T ∩ ({u, v, w, z} : Finset V)).card ≤ 2 := by
        have h_inter : (T ∩ ({u, v, w, z} : Finset V)).card ≤ T.card - 1 := by
          exact Nat.le_sub_one_of_lt ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hxT ) ; aesop ⟩ ) );
        aesop;
      grind

/-
If three triangles pairwise share an edge but do not all share the same edge, they form a K4 structure (union has size 4).
-/
lemma three_triangles_structure {V : Type*} [Fintype V] [DecidableEq V]
    (T0 T1 T2 : Finset V)
    (h0 : T0.card = 3) (h1 : T1.card = 3) (h2 : T2.card = 3)
    (h01 : (T0 ∩ T1).card ≥ 2)
    (h02 : (T0 ∩ T2).card ≥ 2)
    (h12 : (T1 ∩ T2).card ≥ 2)
    (h_not_star : (T0 ∩ T1 ∩ T2).card < 2) :
    (T0 ∪ T1 ∪ T2).card = 4 ∧
    T0 ⊆ (T0 ∪ T1 ∪ T2) ∧ T1 ⊆ (T0 ∪ T1 ∪ T2) ∧ T2 ⊆ (T0 ∪ T1 ∪ T2) := by
      -- Since the intersections are large, we can deduce that the union of the triangles must have size 4.
      have h_card_union : (T0 ∪ T1 ∪ T2).card ≤ 4 := by
        have h_inter : (T0 ∩ (T1 ∪ T2)).card ≥ (T0 ∩ T1 ∪ T0 ∩ T2).card := by
          exact Finset.card_le_card fun x hx => by aesop;
        have := Finset.card_union_add_card_inter ( T0 ∩ T1 ) ( T0 ∩ T2 ) ; simp_all +decide [ Finset.inter_left_comm, Finset.inter_comm ] ;
        grind;
      interval_cases _ : ( T0 ∪ T1 ∪ T2 ).card <;> simp_all +decide;
      · have := Finset.card_le_card ( show T0 ⊆ T0 ∪ ( T1 ∪ T2 ) from Finset.subset_union_left ) ; simp_all +decide ;
      · have := Finset.card_le_card ( Finset.subset_union_left : T0 ⊆ T0 ∪ ( T1 ∪ T2 ) ) ; simp_all +decide ;
      · -- Since the union of the triangles has size 3, each triangle must be equal to the union.
        have h_eq_union : T0 = T0 ∪ (T1 ∪ T2) ∧ T1 = T0 ∪ (T1 ∪ T2) ∧ T2 = T0 ∪ (T1 ∪ T2) := by
          exact ⟨ by exact Finset.eq_of_subset_of_card_le ( Finset.subset_union_left ) ( by linarith ), by exact Finset.eq_of_subset_of_card_le ( Finset.subset_iff.mpr fun x hx => by aesop ) ( by linarith ), by exact Finset.eq_of_subset_of_card_le ( Finset.subset_iff.mpr fun x hx => by aesop ) ( by linarith ) ⟩;
        norm_num [ ← h_eq_union.1, ← h_eq_union.2.1, ← h_eq_union.2.2 ] at *;
        simp_all +decide [ Finset.inter_comm ];
      · aesop_cat

/-
If a pairwise intersecting family of triangles is not a star, there exist three triangles whose union has size 4.
-/
lemma exists_K4_of_not_star {V : Type*} [Fintype V] [DecidableEq V]
    (Tr : Finset (Finset V)) (h_nonempty : Tr.Nonempty)
    (h_tr : ∀ T ∈ Tr, T.card = 3)
    (h_int : ∀ T1 ∈ Tr, ∀ T2 ∈ Tr, (T1 ∩ T2).card ≥ 2)
    (h_not_star : ¬ ∃ u v : V, u ≠ v ∧ ∀ T ∈ Tr, {u, v} ⊆ T) :
    ∃ T0 ∈ Tr, ∃ T1 ∈ Tr, ∃ T2 ∈ Tr, (T0 ∪ T1 ∪ T2).card = 4 := by
      -- Let's pick any three triangles $T0, T1, T2 \in Tr$.
      obtain ⟨T0, hT0⟩ : ∃ T0 ∈ Tr, True := by
        exact ⟨ _, h_nonempty.choose_spec, trivial ⟩
      obtain ⟨T1, hT1, hT1_ne⟩ : ∃ T1 ∈ Tr, T1 ≠ T0 ∧ (T0 ∩ T1).card = 2 := by
        -- Let's choose any $T1 \in Tr$ such that $T1 \neq T0$.
        obtain ⟨T1, hT1, hT1_ne⟩ : ∃ T1 ∈ Tr, T1 ≠ T0 := by
          contrapose! h_not_star; aesop;
          rcases Finset.card_eq_three.mp ( h_tr T0 hT0 ) with ⟨ u, v, w, h ⟩ ; use u, v ; aesop_cat;
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : T0 ∩ T1 ⊆ T0 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : T0 ∩ T1 ⊆ T1 ) ; simp_all +decide ;
        grind
      obtain ⟨T2, hT2, hT2_ne⟩ : ∃ T2 ∈ Tr, T2 ≠ T0 ∧ T2 ≠ T1 ∧ (T0 ∩ T2).card = 2 ∧ (T1 ∩ T2).card = 2 := by
        by_cases hT2 : ∀ T2 ∈ Tr, T2 = T0 ∨ T2 = T1 ∨ (T0 ∩ T2).card = 3 ∨ (T1 ∩ T2).card = 3;
        · -- If for all $T2 \in Tr$, $T2 = T0$ or $T2 = T1$ or $(T0 ∩ T2).card = 3$ or $(T1 ∩ T2).card = 3$, then $Tr$ would be a star.
          have h_star : ∀ T2 ∈ Tr, T2 = T0 ∨ T2 = T1 := by
            intro T2 hT2'; specialize hT2 T2 hT2'; aesop;
            · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : T0 ∩ T2 ⊆ T0 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : T0 ∩ T2 ⊆ T2 ) ; aesop;
            · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : T1 ∩ T2 ⊆ T1 ) ; aesop;
              have := Finset.eq_of_subset_of_card_le this; aesop;
          contrapose! h_not_star;
          obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v ∧ u ∈ T0 ∧ v ∈ T0 ∧ u ∈ T1 ∧ v ∈ T1 := by
            obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card ( T0 ∩ T1 ) ) ; use u, v; aesop;
          exact ⟨ u, v, huv.1, fun T hT => by rcases h_star T hT with ( rfl | rfl ) <;> simp +decide [ *, Finset.insert_subset_iff ] ⟩;
        · push_neg at hT2;
          obtain ⟨ T2, hT2, hT2_ne0, hT2_ne1, hT2_ne3, hT2_ne4 ⟩ := hT2; exact ⟨ T2, hT2, hT2_ne0, hT2_ne1, by have := h_int T0 hT0.1 T2 hT2; have := h_tr T0 hT0.1; have := h_tr T2 hT2; have := Finset.card_le_card ( Finset.inter_subset_left : T0 ∩ T2 ⊆ T0 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : T0 ∩ T2 ⊆ T2 ) ; omega, by have := h_int T1 hT1 T2 hT2; have := h_tr T1 hT1; have := h_tr T2 hT2; have := Finset.card_le_card ( Finset.inter_subset_left : T1 ∩ T2 ⊆ T1 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : T1 ∩ T2 ⊆ T2 ) ; omega ⟩ ;
      grind

/-
If a pairwise intersecting family of triangles contains three triangles sharing a common edge and having distinct third vertices, then every triangle in the family must contain that common edge.
-/
lemma star_of_three_sharing_edge {V : Type*} [Fintype V] [DecidableEq V]
    (Tr : Finset (Finset V))
    (h_tr : ∀ T ∈ Tr, T.card = 3)
    (h_int : ∀ T1 ∈ Tr, ∀ T2 ∈ Tr, (T1 ∩ T2).card ≥ 2)
    (u v w z x : V)
    (h_distinct : ({u, v, w, z, x} : Finset V).card = 5)
    (hA : {u, v, w} ∈ Tr)
    (hB : {u, v, z} ∈ Tr)
    (hC : {u, v, x} ∈ Tr) :
    ∀ T ∈ Tr, {u, v} ⊆ T := by
      -- Suppose there exists T ∈ Tr such that {u, v} ⊈ T.
      intro T hT
      by_contra h_contra;
      -- Since T intersects {u, v, w} in ≥ 2 vertices, and {u, v} ⊈ T, T must contain w and at least one of u, v.
      have hT_w : w ∈ T := by
        have := h_int _ hA _ hT; simp_all +decide [ Finset.subset_iff ] ;
        have := h_int _ hA _ hT; have := Finset.one_lt_card.1 this; aesop;
      have hT_u_or_v : u ∈ T ∨ v ∈ T := by
        specialize h_int _ hT _ hA;
        grind;
      -- Similarly, T must contain z and at least one of u, v, and T must contain x and at least one of u, v.
      have hT_z : z ∈ T := by
        specialize h_int T hT { u, v, z } hB ; simp_all +decide [ Finset.subset_iff ];
        grind
      have hT_x : x ∈ T := by
        have := h_int T hT { u, v, x } hC; simp_all +decide [ Finset.subset_iff ] ;
        have := h_tr T hT; ( have := h_int T hT { u, v, x } hC; ( rw [ Finset.inter_comm ] at this; simp_all ( config := { decide := Bool.true } ) [ Finset.card_eq_three ] ; ) );
        grind
      have hT_u_or_v' : u ∈ T ∨ v ∈ T := by
        exact hT_u_or_v;
      -- So T contains {w, z, x} and some y ∈ {u, v}.
      have hT_subset : {w, z, x} ⊆ T := by
        simp +decide [ *, Finset.insert_subset_iff ];
      have := h_tr T hT; have := Finset.eq_of_subset_of_card_le hT_subset; simp_all +decide ;
      have := Finset.card_insert_le u { v, w, z, x } ; ( have := Finset.card_insert_le v { w, z, x } ; ( have := Finset.card_insert_le w { z, x } ; ( have := Finset.card_insert_le z { x } ; ( have := Finset.card_singleton x ; simp_all +decide ; ) ) ) );
      grind

/-
If a pairwise intersecting family contains two faces of a K4 and is not a star, there exists a third face of the K4 in the family.
-/
lemma third_face_in_K4_of_not_star {V : Type*} [Fintype V] [DecidableEq V]
    (Tr : Finset (Finset V))
    (h_tr : ∀ T ∈ Tr, T.card = 3)
    (h_int : ∀ T1 ∈ Tr, ∀ T2 ∈ Tr, (T1 ∩ T2).card ≥ 2)
    (S : Finset V) (hS : S.card = 4)
    (F1 F2 : Finset V) (hF1 : F1 ∈ Tr) (hF2 : F2 ∈ Tr)
    (hF1S : F1 ⊆ S) (hF2S : F2 ⊆ S) (hneq : F1 ≠ F2)
    (h_not_star : ¬ ∃ u v : V, u ≠ v ∧ ∀ T ∈ Tr, {u, v} ⊆ T) :
    ∃ T3 ∈ Tr, T3 ⊆ S ∧ T3 ≠ F1 ∧ T3 ≠ F2 := by
      -- Let $e = F1 \cap F2 = \{u, v\}$.
      obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v ∧ ({u, v} : Finset V) = F1 ∩ F2 := by
        have := Finset.card_le_card ( Finset.inter_subset_left : F1 ∩ F2 ⊆ F1 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : F1 ∩ F2 ⊆ F2 ) ; simp_all +decide ;
        interval_cases _ : Finset.card ( F1 ∩ F2 ) <;> simp_all +decide;
        · exact absurd ( h_int F1 hF1 F2 hF2 ) ( by simp +decide [ * ] );
        · exact absurd ( h_int F1 hF1 F2 hF2 ) ( by linarith );
        · rw [ Finset.card_eq_two ] at *; tauto;
        · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : F1 ∩ F2 ⊆ F1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : F1 ∩ F2 ⊆ F2 ) ; aesop;
      -- Since not a star, there exists T3 ∈ Tr such that e ⊈ T3.
      obtain ⟨T3, hT3, hT3_not_contain⟩ : ∃ T3 ∈ Tr, ¬({u, v} : Finset V) ⊆ T3 := by
        contrapose! h_not_star; use u, v; aesop;
      -- Since T3 intersects F1 in at least two vertices and e is not a subset of T3, T3 must contain w.
      have hT3w : ∃ w ∈ F1, w ∉ ({u, v} : Finset V) ∧ w ∈ T3 := by
        have hT3w : (F1 ∩ T3).card ≥ 2 := by
          exact h_int F1 hF1 T3 hT3;
        contrapose! hT3w;
        -- Since $F1 \cap T3$ is a subset of $\{u, v\}$, its cardinality is at most 2.
        have hT3w_subset : F1 ∩ T3 ⊆ {u, v} := by
          intro x hx; specialize hT3w x; aesop;
        exact lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ hT3w_subset, fun h => hT3_not_contain <| h ▸ Finset.inter_subset_right ⟩ ) ) ( by simp +decide [ huv.1 ] );
      -- Since T3 intersects F2 in at least two vertices and e is not a subset of T3, T3 must contain z.
      have hT3z : ∃ z ∈ F2, z ∉ ({u, v} : Finset V) ∧ z ∈ T3 := by
        have := h_int F2 hF2 T3 hT3;
        obtain ⟨ z, hz ⟩ := Finset.exists_mem_ne this u;
        by_cases hzv : z = v;
        · obtain ⟨ w, hw ⟩ := Finset.exists_mem_ne this v;
          use w;
          grind;
        · simp +zetaDelta at *;
          exact ⟨ z, hz.1.1, ⟨ hz.2, hzv ⟩, hz.1.2 ⟩;
      refine' ⟨ T3, hT3, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      · intro x hx; specialize h_int _ hT3 _ hF1; specialize h_int; simp_all +decide [ Finset.ext_iff ] ;
        contrapose! h_int;
        have := Finset.card_eq_three.mp ( h_tr _ hT3 ) ; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
        bound;
        all_goals rw [ Finset.card_eq_one.mpr ] ; aesop;
        all_goals simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
        all_goals intro hx; have := hF1S hx; aesop;
      · grind;
      · grind

/-
The intersection of three distinct subsets of size 3 from a set of size 4 has size 1.
-/
lemma intersection_of_three_faces_of_K4 {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.card = 4)
    (F1 F2 F3 : Finset V)
    (hF1 : F1 ⊆ S ∧ F1.card = 3)
    (hF2 : F2 ⊆ S ∧ F2.card = 3)
    (hF3 : F3 ⊆ S ∧ F3.card = 3)
    (h_distinct : F1 ≠ F2 ∧ F1 ≠ F3 ∧ F2 ≠ F3) :
    (F1 ∩ F2 ∩ F3).card = 1 := by
      -- Since F1, F2, F3 are subsets of S of size 3, and |S|=4, each is of the form S \ {x} for some x in S.
      obtain ⟨x, hx⟩ : ∃ x ∈ S, F1 = S \ {x} := by
        -- Since $F1$ is a subset of $S$ with cardinality 3 and $S$ has cardinality 4, there must exist an element $x \in S$ such that $x \notin F1$.
        obtain ⟨x, hx⟩ : ∃ x ∈ S, x ∉ F1 := by
          exact Finset.exists_of_ssubset ( hF1.1.ssubset_of_ne ( by aesop_cat ) );
        use x; aesop;
        rw [ Finset.eq_of_subset_of_card_le ( show F1 ⊆ S \ { x } from fun y hy => Finset.mem_sdiff.mpr ⟨ left hy, by aesop ⟩ ) ( by rw [ Finset.card_sdiff ] ; aesop ) ]
      obtain ⟨y, hy⟩ : ∃ y ∈ S, F2 = S \ {y} := by
        -- Since $F2$ is a subset of $S$ with cardinality 3, and $S$ has 4 elements, $F2$ must be $S$ minus one element.
        have hF2_elements : ∃ y ∈ S, F2 = S \ {y} := by
          have h_card_diff : (S \ F2).card = 1 := by
            grind
          obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_card_diff;
          exact ⟨ y, Finset.mem_sdiff.mp ( hy.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← hy, Finset.sdiff_sdiff_eq_self hF2.1 ] ⟩;
        exact hF2_elements
      obtain ⟨z, hz⟩ : ∃ z ∈ S, F3 = S \ {z} := by
        -- Since F3 is a subset of S with 3 elements, the complement of F3 in S must be a singleton set.
        have h_compl_singleton : (S \ F3).card = 1 := by
          grind;
        obtain ⟨ z, hz ⟩ := Finset.card_eq_one.mp h_compl_singleton;
        exact ⟨ z, Finset.mem_sdiff.mp ( hz.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← hz, Finset.sdiff_sdiff_eq_self hF3.1 ] ⟩;
      simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
      by_cases hxz : x = z <;> by_cases hyz : y = z <;> simp_all +decide [ Finset.ext_iff ];
      by_cases hxy : x = y <;> simp_all +decide [ Finset.inter_erase ]

/-
If a triangle intersects three distinct faces of a K4 in at least 2 vertices each, it is contained in the K4.
-/
lemma K4_of_three_faces {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.card = 4)
    (F1 F2 F3 : Finset V)
    (hF1 : F1 ⊆ S ∧ F1.card = 3)
    (hF2 : F2 ⊆ S ∧ F2.card = 3)
    (hF3 : F3 ⊆ S ∧ F3.card = 3)
    (h_distinct : F1 ≠ F2 ∧ F1 ≠ F3 ∧ F2 ≠ F3)
    (T : Finset V) (hT : T.card = 3)
    (h_int1 : (T ∩ F1).card ≥ 2)
    (h_int2 : (T ∩ F2).card ≥ 2)
    (h_int3 : (T ∩ F3).card ≥ 2) :
    T ⊆ S := by
      -- Since $F1$, $F2$, and $F3$ are distinct subsets of $S$ with 3 elements each, their intersection must have exactly 1 element.
      have h_inter : (F1 ∩ F2 ∩ F3).card = 1 := by
        exact?;
      -- Let $u$ be the unique element in $F1 \cap F2 \cap F3$.
      obtain ⟨u, hu⟩ : ∃ u, u ∈ F1 ∩ F2 ∩ F3 ∧ ∀ v, v ∈ F1 ∩ F2 ∩ F3 → v = u := by
        rw [ Finset.card_eq_one ] at h_inter; obtain ⟨ u, hu ⟩ := h_inter; use u; aesop;
      -- Since $F1$, $F2$, and $F3$ are subsets of $S$ and their intersection is $\{u\}$, we can write $F1 = S \setminus \{x\}$, $F2 = S \setminus \{y\}$, $F3 = S \setminus \{z\}$ for some $x, y, z \in S \setminus \{u\}$.
      obtain ⟨x, y, z, hx, hy, hz⟩ : ∃ x y z, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ≠ u ∧ y ≠ u ∧ z ≠ u ∧ F1 = S \ {x} ∧ F2 = S \ {y} ∧ F3 = S \ {z} := by
        -- Since $F1$, $F2$, and $F3$ are subsets of $S$ and their intersection is $\{u\}$, we can write $F1 = S \setminus \{x\}$, $F2 = S \setminus \{y\}$, $F3 = S \setminus \{z\}$ for some $x, y, z \in S \setminus \{u\}$ by definition of set difference.
        have hF1_def : ∃ x, x ∈ S ∧ x ∉ F1 ∧ F1 = S \ {x} := by
          have hF1_def : Finset.card (S \ F1) = 1 := by
            grind;
          obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp hF1_def;
          exact ⟨ x, Finset.mem_sdiff.mp ( hx.symm ▸ Finset.mem_singleton_self _ ) |>.1, Finset.mem_sdiff.mp ( hx.symm ▸ Finset.mem_singleton_self _ ) |>.2, by rw [ ← hx, Finset.sdiff_sdiff_eq_self hF1.1 ] ⟩
        have hF2_def : ∃ y, y ∈ S ∧ y ∉ F2 ∧ F2 = S \ {y} := by
          obtain ⟨y, hy⟩ : ∃ y ∈ S, y ∉ F2 := by
            exact Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ hF2.1, by aesop_cat ⟩ );
          refine' ⟨ y, hy.1, hy.2, _ ⟩;
          rw [ Finset.eq_of_subset_of_card_le ( show F2 ⊆ S \ { y } from fun x hx => Finset.mem_sdiff.mpr ⟨ hF2.1 hx, by aesop ⟩ ) ] ; simp +decide [ *, Finset.card_sdiff ]
        have hF3_def : ∃ z, z ∈ S ∧ z ∉ F3 ∧ F3 = S \ {z} := by
          have hF3_def : ∃ z, z ∈ S ∧ z∉F3 := by
            exact Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ hF3.1, by aesop_cat ⟩ );
          obtain ⟨ z, hz1, hz2 ⟩ := hF3_def;
          refine' ⟨ z, hz1, hz2, Finset.eq_of_subset_of_card_le ( fun x hx => by aesop ) ( by simp +decide [ *, Finset.card_sdiff ] ) ⟩;
        grind;
      -- Since $F1 = S \setminus \{x\}$, $F2 = S \setminus \{y\}$, and $F3 = S \setminus \{z\}$, we can write $F1 = \{u, y, z\}$, $F2 = \{u, x, z\}$, and $F3 = \{u, x, y\}$.
      have hF1_eq : F1 = {u, y, z} := by
        rw [ Finset.eq_of_subset_of_card_le ( show { u, y, z } ⊆ S \ { x } from by aesop_cat ) ] ; aesop_cat;
        rw [ Finset.card_sdiff ] ; aesop
      have hF2_eq : F2 = {u, x, z} := by
        grind +ring
      have hF3_eq : F3 = {u, x, y} := by
        grind;
      -- Apply `K4_intersecting` with vertices $u$, $x$, $y$, $z$.
      have h_T_subset_S : T ⊆ {u, x, y, z} := by
        apply_rules [ K4_intersecting ];
        · grind;
        · simp_all +decide [ Finset.inter_comm ];
        · simpa only [ Finset.inter_comm, hF2_eq ] using h_int2;
        · simpa only [ hF1_eq, Finset.inter_comm ] using h_int1;
      grind

/-
If a family of triangles is pairwise intersecting, then either they form a star (share an edge) or they are all contained in a K4 (set of 4 vertices).
-/
lemma pairwise_intersecting_triangles_structure {V : Type*} [Fintype V] [DecidableEq V]
    (Tr : Finset (Finset V)) (h_nonempty : Tr.Nonempty)
    (h_tr : ∀ T ∈ Tr, T.card = 3)
    (h_int : ∀ T1 ∈ Tr, ∀ T2 ∈ Tr, (T1 ∩ T2).card ≥ 2) :
    (∃ u v : V, u ≠ v ∧ ∀ T ∈ Tr, {u, v} ⊆ T) ∨
    (∃ S : Finset V, S.card = 4 ∧ ∀ T ∈ Tr, T ⊆ S) := by
      by_contra h_contra;
      -- By `exists_K4_of_not_star`, there exist T0, T1, T2 in Tr such that S = T0 ∪ T1 ∪ T2 has size 4.
      obtain ⟨S, hS⟩ : ∃ S : Finset V, S.card = 4 ∧ ∃ T0 ∈ Tr, ∃ T1 ∈ Tr, ∃ T2 ∈ Tr, T0 ∪ T1 ∪ T2 = S := by
        obtain ⟨T0, hT0, T1, hT1, T2, hT2, hS⟩ : ∃ T0 ∈ Tr, ∃ T1 ∈ Tr, ∃ T2 ∈ Tr, (T0 ∪ T1 ∪ T2).card = 4 := by
          apply exists_K4_of_not_star Tr h_nonempty h_tr h_int (by
          exact fun h => h_contra <| Or.inl h);
        exact ⟨ _, hS, _, hT0, _, hT1, _, hT2, rfl ⟩;
      -- Let F_set = {T0, T1, T2}.
      obtain ⟨T0, hT0, T1, hT1, T2, hT2, hS_eq⟩ := hS.right;
      -- Since union is size 4, F_set must contain at least 2 distinct sets (if all equal, union size 3).
      obtain ⟨F1, F2, hF1, hF2, hneq⟩ : ∃ F1 F2 : Finset V, F1 ∈ Tr ∧ F2 ∈ Tr ∧ F1 ⊆ S ∧ F2 ⊆ S ∧ F1 ≠ F2 := by
        by_cases h_eq : T0 = T1 ∧ T1 = T2;
        · grind;
        · by_cases h_eq : T0 = T1;
          · exact ⟨ T0, T2, hT0, hT2, hS_eq ▸ Finset.subset_union_left.trans ( Finset.subset_union_left ), hS_eq ▸ Finset.subset_union_right, by aesop ⟩;
          · use T0, T1;
            aesop;
            exact fun x hx => Finset.mem_union_right _ ( Finset.mem_union_left _ hx );
      -- By `third_face_in_K4_of_not_star`, there exists T3 in Tr such that T3 ⊆ S, T3 ≠ F1, T3 ≠ F2.
      obtain ⟨T3, hT3, hT3S, hT3_ne⟩ : ∃ T3 ∈ Tr, T3 ⊆ S ∧ T3 ≠ F1 ∧ T3 ≠ F2 := by
        apply third_face_in_K4_of_not_star Tr h_tr h_int S hS.left F1 F2 hF1 hF2 hneq.left hneq.right.left hneq.right.right;
        exact fun ⟨ u, v, huv, h ⟩ => h_contra <| Or.inl ⟨ u, v, huv, h ⟩;
      -- Now we have 3 distinct faces F1, F2, F3 in Tr, all subsets of S.
      have h_distinct_faces : F1 ≠ F2 ∧ F1 ≠ T3 ∧ F2 ≠ T3 := by
        tauto;
      -- Let T be any triangle in Tr.
      have hT_subset_S : ∀ T ∈ Tr, T ⊆ S := by
        exact fun T hT => K4_of_three_faces S hS.1 F1 F2 T3 ⟨ hneq.1, h_tr F1 hF1 ⟩ ⟨ hneq.2.1, h_tr F2 hF2 ⟩ ⟨ hT3S, h_tr T3 hT3 ⟩ h_distinct_faces T ( h_tr T hT ) ( h_int T hT F1 hF1 ) ( h_int T hT F2 hF2 ) ( h_int T hT T3 hT3 );
      exact h_contra <| Or.inr ⟨ S, hS.1, hT_subset_S ⟩

/-
If all triangles of a graph are contained in a set of 4 vertices, then the triangle covering number is at most 2.
-/
lemma tuza_case_nu_1_K4_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.card = 4)
    (h_subset : ∀ T ∈ G.cliqueFinset 3, T ⊆ S) :
    triangleCoveringNumber G ≤ 2 := by
      have h_triangle_cover : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ T.sym2 := by
        -- Let's choose any two edges from the set of pairs P = {{u, v}, {w, z}}.
        obtain ⟨u, v, w, z, h_distinct⟩ : ∃ u v w z : V, u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧ S = {u, v, w, z} := by
          exact?;
        set P : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, z)} with hP_def
        have hP_subset : ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ P, e ∈ T.sym2 := by
          intro T hT; specialize h_subset T hT; simp_all +decide [ Finset.subset_iff ] ;
          rcases Finset.card_eq_three.mp hT.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; aesop;
        refine' ⟨ P.filter fun e => e ∈ G.edgeFinset, _, _, _ ⟩;
        · exact fun x hx => Finset.mem_filter.mp hx |>.2;
        · exact le_trans ( Finset.card_filter_le _ _ ) ( Finset.card_insert_le _ _ );
        · intro T hT; obtain ⟨ e, he₁, he₂ ⟩ := hP_subset T hT; use e; aesop;
          · exact hT.1 ( by aesop ) ( by aesop ) ( by aesop );
          · exact hT.1 ( by aesop ) ( by aesop ) ( by aesop );
      obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_triangle_cover;
      unfold triangleCoveringNumber;
      refine' Nat.le_trans ( _ : _ ≤ _ ) hE₂;
      have h_min_le : (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)).min ≤ some E'.card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE₁, ⟨ hE₁, hE₃ ⟩ ⟩, rfl ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop;
      exact WithTop.coe_le_coe.mp h_min_le

end AristotleLemmas

theorem tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  -- Since trianglePackingNumber G = 1, the set of triangles Tr = G.cliqueFinset 3 is nonempty.
  have h_nonempty : (G.cliqueFinset 3).Nonempty := by
    contrapose! h; aesop;
    -- Since $G$ is $K_3$-free, its triangle packing number is zero.
    have h_clique_free : G.cliqueFinset 3 = ∅ := by
      exact Finset.eq_empty_of_forall_notMem fun t ht => h _ <| by simpa using ht;
    unfold trianglePackingNumber at a ; aesop;
    simp_all +decide [ Finset.filter_singleton, isTrianglePacking ];
  -- By `pairwise_intersecting_triangles_structure`, Tr is either a star or contained in a K4.
  have h_structure : (∃ u v : V, u ≠ v ∧ ∀ T ∈ G.cliqueFinset 3, {u, v} ⊆ T) ∨ (∃ S : Finset V, S.card = 4 ∧ ∀ T ∈ G.cliqueFinset 3, T ⊆ S) := by
    apply pairwise_intersecting_triangles_structure;
    · exact h_nonempty;
    · simp +decide [ SimpleGraph.cliqueFinset ];
      exact fun T hT => hT.2;
    · intro T1 hT1 T2 hT2; contrapose! h; aesop;
      -- Since {T1, T2} is a triangle packing of size 2, this contradicts the assumption that the triangle packing number is 1.
      have h_contradiction : ∃ S : Finset (Finset V), S ⊆ G.cliqueFinset 3 ∧ S.card = 2 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
        use {T1, T2};
        rw [ Finset.insert_subset_iff, Finset.singleton_subset_iff ] ; aesop;
        · rw [ Finset.card_pair ] ; aesop;
          exact h.not_le ( hT2.card_eq.symm ▸ by decide );
        · intro t ht t' ht' hne; aesop;
          · linarith;
          · rw [ Finset.inter_comm ] ; exact Nat.le_of_lt_succ h;
      obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_contradiction;
      have h_contradiction : (Finset.image Finset.card (Finset.filter (fun S => isTrianglePacking G S) (Finset.powerset (G.cliqueFinset 3)))).max ≥ 2 := by
        refine' Finset.le_max _ ; aesop;
        exact ⟨ S, ⟨ hS₁, ⟨ hS₁, hS₃ ⟩ ⟩, hS₂ ⟩;
      unfold trianglePackingNumber at a ; aesop;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  unfold triangleCoveringNumber at *; aesop;
  · -- Let $E' = \{ \{w, w_1\} \}$. We need to show that $E'$ is a triangle cover.
    have h_cover : isTriangleCover G {Sym2.mk (w, w_1)} := by
      constructor <;> aesop;
      obtain ⟨ T, hT ⟩ := h_nonempty; specialize right T; rw [ Finset.subset_iff ] at right; aesop;
      exact hT.1 ( by aesop ) ( by aesop ) ( by aesop );
    have h_min : (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)).min ≤ 1 := by
      refine' Finset.min_le _;
      simp +zetaDelta at *;
      exact ⟨ { s(w, w_1) }, ⟨ by simpa using h_cover.1, h_cover ⟩, by simp +decide ⟩;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop;
    interval_cases a <;> trivial;
  · have := tuza_case_nu_1_K4_subgraph G w left ( by aesop ) ; aesop;

/- Aristotle failed to find a proof. -/
-- Case ν = 2: Two packing triangles, τ ≤ 4
theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

/- Aristotle failed to find a proof. -/
-- Case ν = 3: Three packing triangles, τ ≤ 6
theorem tuza_case_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 3) : triangleCoveringNumber G ≤ 6 := by
  sorry

-- Main theorem: combine cases
theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt2 | heq2
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt2) with hlt3 | heq3
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt3) with hlt4 | heq4
        · omega
        · simp only [heq4, mul_zero]; exact (tuza_case_nu_0 G heq4).le
      · simp only [heq3, mul_one]; exact tuza_case_nu_1 G heq3
    · simp only [heq2]; norm_num; exact tuza_case_nu_2 G heq2
  · simp only [heq]; norm_num; exact tuza_case_nu_3 G heq

end