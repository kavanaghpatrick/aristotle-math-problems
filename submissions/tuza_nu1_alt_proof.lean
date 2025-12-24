/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7f9d358e-f2cc-4094-b560-709d55a7af1d

The following was proved by Aristotle:

- theorem tuza_conjecture_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu_1 : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2
-/

/-
ITERATION 3 ALT for Tuza's Conjecture - τ ≤ 2ν
Alternative approach with more explicit proof structure

Key difference: More explicit case analysis for k4_is_maximal_if_nu_1
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

-- Abbreviated: All lemmas from iteration 2 that were proven by Aristotle
-- (tuza_base_case, triangleCoveringNumber_le_card_add_deleteEdges, exists_max_packing,
--  packing_one_implies_intersect, k4_tau_le_2, intersect_triangles_aux,
--  k4_of_intersecting_triangles, exists_triangle_disjoint_from_pair,
--  exists_triangles_for_k4_of_tau_gt_2)

-- For brevity, we include these as sorry'd placeholders that Aristotle already proved:

lemma packing_one_implies_intersect {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  -- PROVEN IN ITERATION 2
  contrapose! h;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨ h1, Finset.singleton_subset_iff.mpr h2 ⟩, _ ⟩ ) );
  · rw [ Finset.card_pair ] ; aesop;
    unfold triangleEdges at h; aesop;
    simp_all +decide [ Finset.ext_iff ];
    have := Finset.card_eq_three.mp h2.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; specialize h a b; aesop;
  · intro x hx y hy hxy; aesop;
    exact h.symm

lemma k4_tau_le_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w x : V) (h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x)
    (h_edges : G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x)
    (h_triangles : G.cliqueFinset 3 = { {u,v,w}, {u,v,x}, {u,w,x}, {v,w,x} }) :
    triangleCoveringNumber G ≤ 2 := by
  -- PROVEN IN ITERATION 2
  have h_delete_edges : IsTriangleCovering G ({Sym2.mk (u, v), Sym2.mk (w, x)} : Finset (Sym2 V)) := by
    simp_all +decide [ Finset.ext_iff, IsTriangleCovering ];
    simp_all +decide [ SimpleGraph.isNClique_iff ];
    intro a ha; specialize h_triangles a; simp_all +decide [ SimpleGraph.isClique_iff, Set.Pairwise ] ;
    grind;
  unfold triangleCoveringNumber;
  have h_card : 2 ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
    simp +zetaDelta at *;
    refine' ⟨ { Sym2.mk ( u, v ), Sym2.mk ( w, x ) }, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
  have := Finset.min_le h_card; aesop;
  cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop

/-
CRITICAL LEMMA - k4_is_maximal_if_nu_1 - ALTERNATIVE PROOF APPROACH

Strategy: Prove by showing any triangle t must be a subset of {u,v,w,x}.

Key insight: The K₄ triangles partition the 6 edges:
  - {u,v,w}: edges {u,v}, {u,w}, {v,w}
  - {u,v,x}: edges {u,v}, {u,x}, {v,x}
  - {u,w,x}: edges {u,w}, {u,x}, {w,x}
  - {v,w,x}: edges {v,w}, {v,x}, {w,x}

If t shares an edge with ALL of these, t must use K₄ edges.
A triangle with an external vertex y can only share edges {a,b} where a,b ∈ {u,v,w,x}.
But for each edge {a,b} in K₄, there's a K₄ triangle NOT containing {a,b}:
  - {u,v} is NOT in {u,w,x} or {v,w,x}
  - {u,w} is NOT in {u,v,x} or {v,w,x}
  - {u,x} is NOT in {u,v,w} or {v,w,x}
  - {v,w} is NOT in {u,v,x} or {u,w,x}
  - {v,x} is NOT in {u,v,w} or {u,w,x}
  - {w,x} is NOT in {u,v,w} or {u,v,x}

So if t = {a,b,y} with y external, t can't share an edge with ALL K₄ triangles.
-/
lemma k4_is_maximal_if_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w x : V) (h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x)
    (h_edges : G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x)
    (h_nu_1 : trianglePackingNumber G = 1) :
    ∀ t ∈ G.cliqueFinset 3, t ∈ ({ {u,v,w}, {u,v,x}, {u,w,x}, {v,w,x} } : Finset (Finset V)) := by
  intro t ht
  -- The 4 K₄ triangles are in G.cliqueFinset 3
  have h_uvw_in : ({u,v,w} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  have h_uvx_in : ({u,v,x} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  have h_uwx_in : ({u,w,x} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  have h_vwx_in : ({v,w,x} : Finset V) ∈ G.cliqueFinset 3 := by
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
  -- t must share an edge with each K₄ triangle (by ν=1)
  have h1 : ¬ Disjoint (triangleEdges t) (triangleEdges {u,v,w}) := packing_one_implies_intersect G h_nu_1 t {u,v,w} ht h_uvw_in
  have h2 : ¬ Disjoint (triangleEdges t) (triangleEdges {u,v,x}) := packing_one_implies_intersect G h_nu_1 t {u,v,x} ht h_uvx_in
  have h3 : ¬ Disjoint (triangleEdges t) (triangleEdges {u,w,x}) := packing_one_implies_intersect G h_nu_1 t {u,w,x} ht h_uwx_in
  have h4 : ¬ Disjoint (triangleEdges t) (triangleEdges {v,w,x}) := packing_one_implies_intersect G h_nu_1 t {v,w,x} ht h_vwx_in
  -- t has 3 vertices: a, b, c
  have ht_card : t.card = 3 := ht.2
  obtain ⟨a, b, c, hab, hac, hbc, ht_eq⟩ := Finset.card_eq_three.mp ht_card
  -- From h1-h4, t shares an edge with each K₄ triangle
  -- This means t's edges must overlap with each of:
  --   triangleEdges {u,v,w} = {{u,v}, {u,w}, {v,w}}
  --   triangleEdges {u,v,x} = {{u,v}, {u,x}, {v,x}}
  --   triangleEdges {u,w,x} = {{u,w}, {u,x}, {w,x}}
  --   triangleEdges {v,w,x} = {{v,w}, {v,x}, {w,x}}
  -- t has edges: {{a,b}, {a,c}, {b,c}}
  -- For t to share an edge with {u,v,w} AND {v,w,x}, the shared edges must be:
  --   with {u,v,w}: one of {u,v}, {u,w}, {v,w}
  --   with {v,w,x}: one of {v,w}, {v,x}, {w,x}
  -- The only common edge is {v,w}
  -- So either t contains {v,w}, OR t contains edges from both lists separately
  -- But t only has 3 edges, so it can contain at most 3 of the 6 K₄ edges
  -- Analysis: if t contains {v,w}, check which other edges it can have
  -- Continue this analysis...
  -- Ultimately: t must be one of the 4 K₄ triangles
  simp_all +decide [triangleEdges, Finset.disjoint_left]
  -- Use the non-disjoint constraints to derive that {a,b,c} ∈ {{u,v,w}, {u,v,x}, {u,w,x}, {v,w,x}}
  simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  simp_all +decide [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton]
  -- The constraints from h1-h4 force t into the K₄ structure
  -- Case analysis on which K₄ vertex is NOT in t
  -- If u ∉ t: t must share edge with {u,v,w} and {u,v,x} and {u,w,x}
  --   {u,v,w} ∩ edges = {{v,w}} if u ∉ t
  --   {u,v,x} ∩ edges = {{v,x}} if u ∉ t
  --   {u,w,x} ∩ edges = {{w,x}} if u ∉ t
  --   So t contains {v,w}, {v,x}, {w,x} => t = {v,w,x}
  -- Similarly for v ∉ t, w ∉ t, x ∉ t
  -- Otherwise all of u,v,w,x ∈ t, but t has only 3 vertices, contradiction
  grind

lemma k4_implies_tau_le_2_if_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w x : V) (h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x)
    (h_edges : G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x)
    (h_nu_1 : trianglePackingNumber G = 1) :
    triangleCoveringNumber G ≤ 2 := by
  apply k4_tau_le_2 G u v w x h_distinct h_edges
  ext t
  constructor
  · intro ht
    exact k4_is_maximal_if_nu_1 G u v w x h_distinct h_edges h_nu_1 t ht
  · intro ht
    simp_all +decide [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]
    rcases ht with rfl | rfl | rfl | rfl <;> simp_all +decide

-- Main theorem: If ν(G) = 1, then τ(G) ≤ 2
noncomputable section AristotleLemmas

/-
If the triangle packing number is 1, and we have two triangles {u,v,w} and {v,w,x}, then any third triangle t3 that does not contain the edge {v,w} must be either {u,v,x} or {u,w,x}.
-/
lemma third_triangle_forces_k4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w x : V) (h_distinct : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x)
    (h_t1 : {u,v,w} ∈ G.cliqueFinset 3)
    (h_t2 : {v,w,x} ∈ G.cliqueFinset 3)
    (h_nu_1 : trianglePackingNumber G = 1)
    (t3 : Finset V) (h_t3 : t3 ∈ G.cliqueFinset 3)
    (h_avoid : Sym2.mk (v, w) ∉ triangleEdges t3) :
    t3 = {u,v,x} ∨ t3 = {u,w,x} := by
      have h_cases : (s(u, v) ∈ triangleEdges t3 ∧ s(v, x) ∈ triangleEdges t3) ∨ (s(u, w) ∈ triangleEdges t3 ∧ s(w, x) ∈ triangleEdges t3) := by
        have h_cases : (s(u, v) ∈ triangleEdges t3 ∨ s(u, w) ∈ triangleEdges t3) ∧ (s(v, x) ∈ triangleEdges t3 ∨ s(w, x) ∈ triangleEdges t3) := by
          aesop;
          · have h_edges : ¬Disjoint (triangleEdges t3) (triangleEdges {u, v, w}) := by
              apply packing_one_implies_intersect G h_nu_1 t3 {u, v, w};
              · aesop;
              · aesop;
            simp_all +decide [ Finset.disjoint_left, triangleEdges ];
            rcases h_edges with ⟨ x, y, hy, z, hz, hne, rfl, h | h | h ⟩ <;> simp_all +decide [ Sym2.eq_swap ];
            · grind;
            · grind;
            · grind;
          · have h_cases : ¬Disjoint (triangleEdges t3) (triangleEdges {v, w, x}) := by
              exact packing_one_implies_intersect G h_nu_1 t3 { v, w, x } ( by aesop ) ( by aesop );
            simp_all +decide [ Finset.disjoint_left, triangleEdges ];
            rcases h_cases with ⟨ y, z, hz, w, hw, hne, rfl, h | h | h | h ⟩ <;> simp_all +decide [ Sym2.eq_swap ];
            · grind;
            · grind;
            · grind;
            · grind +ring;
        unfold triangleEdges at *; simp_all +decide [ Finset.mem_image, Finset.mem_offDiag, Sym2.eq_iff ] ;
        grind +ring;
      aesop;
      · -- Since $u, v, x \in t3$ and $t3$ has exactly 3 elements, we must have $t3 = \{u, v, x\}$.
        have h_t3_subset : u ∈ t3 ∧ v ∈ t3 ∧ x ∈ t3 := by
          unfold triangleEdges at *; aesop;
        have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ h_t3_subset.1, Finset.insert_subset_iff.mpr ⟨ h_t3_subset.2.1, Finset.singleton_subset_iff.mpr h_t3_subset.2.2 ⟩ ⟩ ) ; aesop;
        exact Or.inl <| Eq.symm <| this <| by linarith [ h_t3.2 ] ;
      · -- Since $t3$ is a triangle, it must contain three vertices. We know that $u$, $w$, and $x$ are all in $t3$ because $s(u, w)$ and $s(w, x)$ are in the triangleEdges of $t3$.
        have h_vertices : u ∈ t3 ∧ w ∈ t3 ∧ x ∈ t3 := by
          unfold triangleEdges at *; aesop;
        have := h_t3.1; ( have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ h_vertices.1, Finset.insert_subset_iff.mpr ⟨ h_vertices.2.1, Finset.singleton_subset_iff.mpr h_vertices.2.2 ⟩ ⟩ ) ; aesop; );
        have := h_t3.2; aesop;

/-
If the triangle packing number is 1 and the covering number is greater than 1, then there exists a K4 subgraph.
-/
lemma exists_k4_of_nu_1_and_tau_gt_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu_1 : trianglePackingNumber G = 1) (h_tau_gt_1 : triangleCoveringNumber G > 1) :
    ∃ u v w x : V, u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x ∧
    G.Adj u v ∧ G.Adj u w ∧ G.Adj u x ∧ G.Adj v w ∧ G.Adj v x ∧ G.Adj w x := by
      -- Since $\nu(G) = 1$, there exists a triangle $t_1 = \{u,v,w\}$.
      obtain ⟨u, v, w, huv, huw, hvw⟩ : ∃ u v w : V, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ G.Adj u v ∧ G.Adj u w ∧ G.Adj v w := by
        -- Since $\tau(G) > 1$, there exists a triangle $t_1$.
        obtain ⟨t1, ht1⟩ : ∃ t1 ∈ G.cliqueFinset 3, True := by
          contrapose! h_nu_1;
          unfold trianglePackingNumber;
          rw [ Finset.eq_empty_of_forall_not_mem h_nu_1 ] ; aesop;
          rw [ Finset.filter_singleton ] at a ; aesop;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        rcases Finset.card_eq_three.mp ht1.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v, by aesop, w ; aesop;
      -- Since $\{u,v\}$ is not a cover (otherwise $\tau(G) \le 1$), there exists a triangle $t_2$ that does not contain the edge $\{u,v\}$.
      obtain ⟨t2, ht2, ht2_not_uv⟩ : ∃ t2 : Finset V, t2 ∈ G.cliqueFinset 3 ∧ Sym2.mk (u, v) ∉ triangleEdges t2 := by
        -- If the covering number is greater than 1, then there exists a triangle $t_2$ that does not contain the edge $\{u,v\}$.
        have h_not_cover : ¬(IsTriangleCovering G {Sym2.mk (u, v)}) := by
          intro h;
          -- If $\{u,v\}$ is a triangle cover, then $\tau(G) \leq 1$, contradicting $\tau(G) > 1$.
          have h_contra : triangleCoveringNumber G ≤ 1 := by
            unfold triangleCoveringNumber;
            have h_contra : {Sym2.mk (u, v)} ∈ Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset := by
              aesop;
            have h_contra : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ 1 := by
              exact Finset.min_le ( Finset.mem_image.mpr ⟨ _, h_contra, rfl ⟩ );
            cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
          linarith;
        unfold IsTriangleCovering at h_not_cover;
        simp_all +decide [ Finset.ext_iff, SimpleGraph.cliqueFinset ];
        obtain ⟨ t2, ht2 ⟩ := h_not_cover; use t2; simp_all +decide [ SimpleGraph.isNClique_iff, triangleEdges ] ;
        have := Finset.card_eq_three.mp ht2.2; obtain ⟨ x, y, z, hxy, hyz, hxz ⟩ := this; simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.deleteEdges ] ;
        grind;
      -- Since $t2$ does not contain the edge $\{u,v\}$, it must contain $\{u,w\}$ or $\{v,w\}$.
      by_cases h_t2_uw : Sym2.mk (u, w) ∈ triangleEdges t2;
      · -- Since $t2$ contains the edge $\{u,w\}$, it must be of the form $\{u,w,x\}$ for some $x$.
        obtain ⟨x, hx⟩ : ∃ x : V, t2 = {u, w, x} := by
          simp +zetaDelta at *;
          -- Since $t2$ is a clique of size 3 and contains $u$ and $w$, the third element must be some $x$.
          obtain ⟨x, hx⟩ : ∃ x : V, t2 = {u, w, x} := by
            have h_card : t2.card = 3 := by
              exact ht2.2
            have h_uw : u ∈ t2 ∧ w ∈ t2 := by
              unfold triangleEdges at h_t2_uw; aesop;
            obtain ⟨x, hx⟩ : ∃ x : V, t2 = {u, w, x} := by
              have h_card : t2.card = 3 := h_card
              have h_uw : u ∈ t2 ∧ w ∈ t2 := h_uw
              have h_third : ∃ x : V, x ∈ t2 ∧ x ≠ u ∧ x ≠ w := by
                exact Exists.imp ( by aesop ) ( Finset.exists_ne_of_one_lt_card ( show 1 < Finset.card ( t2.erase u ) from by rw [ Finset.card_erase_of_mem h_uw.1, h_card ] ; decide ) w )
              obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_third; use x; rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ h_uw.1, Finset.insert_subset_iff.mpr ⟨ h_uw.2, Finset.singleton_subset_iff.mpr hx₁ ⟩ ⟩ ) ] ; aesop;
              rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
            use x;
          use x;
        -- Since $\{u,w\}$ is not a cover (otherwise $\tau(G) \le 1$), there exists a triangle $t_3$ that does not contain the edge $\{u,w\}$.
        obtain ⟨t3, ht3, ht3_not_uw⟩ : ∃ t3 : Finset V, t3 ∈ G.cliqueFinset 3 ∧ Sym2.mk (u, w) ∉ triangleEdges t3 := by
          contrapose! h_tau_gt_1;
          -- If every triangle in $G$ contains the edge $\{u,w\}$, then $\{u,w\}$ is a triangle cover.
          have h_cover : IsTriangleCovering G {Sym2.mk (u, w)} := by
            ext t; simp [IsTriangleCovering];
            simp_all +decide [ SimpleGraph.isNClique_iff, SimpleGraph.deleteEdges ];
            intro ht ht'; specialize h_tau_gt_1 t; simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.fromEdgeSet ] ;
            simp_all +decide [ Set.Pairwise, triangleEdges ];
            grind;
          unfold triangleCoveringNumber;
          have h_card : Finset.card {Sym2.mk (u, w)} ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
            simp +zetaDelta at *;
            exact ⟨ { s(u, w) }, ⟨ by aesop_cat, h_cover ⟩, by aesop_cat ⟩;
          have h_min : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ 1 := by
            exact Finset.min_le h_card |> le_trans <| by norm_num;
          cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
        -- By `third_triangle_forces_k4`, $t3$ must be $\{u,v,x\}$ or $\{v,w,x\}$.
        have h_t3_cases : t3 = {u, v, x} ∨ t3 = {v, w, x} := by
          have := third_triangle_forces_k4 G v u w x; aesop;
          by_cases hvx : v = x <;> by_cases hux : u = x <;> by_cases hwu : w = u <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          · bound;
            exact False.elim <| ht2_not_uv <| Finset.mem_image.mpr ⟨ ( u, v ), by aesop ⟩;
          · specialize this ( Ne.symm huv ) ( by aesop ) ( by simpa [ SimpleGraph.adj_comm ] using left_1 ) t3 ht3.1 ht3.2 ht3_not_uw ; aesop;
        rcases h_t3_cases with ( rfl | rfl ) <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
        · use u, v, huv, w, huw, x;
          simp_all +decide [ SimpleGraph.isNClique_iff ];
          by_cases hu : u = x <;> by_cases hv : v = x <;> by_cases hw : w = x <;> simp_all +decide;
        · use u, v, huv, w, huw, x;
          simp_all +decide [ SimpleGraph.isNClique_iff ];
          by_cases hu : u = x <;> by_cases hv : v = x <;> by_cases hw : w = x <;> simp_all +decide;
      · -- Since $t2$ does not contain the edge $\{u,v\}$ and $\{u,w\}$, it must contain $\{v,w\}$.
        have h_t2_vw : Sym2.mk (v, w) ∈ triangleEdges t2 := by
          have := packing_one_implies_intersect G h_nu_1 { u, v, w } t2; simp_all +decide [ Finset.mem_powerset, Finset.subset_iff ] ;
          simp_all +decide [ Finset.disjoint_left, triangleEdges ];
          rcases this ( by
            simp_all +decide [ SimpleGraph.isNClique_iff ] ) with ⟨ x, hx ⟩ ; rcases hx with ( ( ⟨ rfl, y, hy, z, hz, hyz, h ⟩ | ⟨ rfl, y, hy, z, hz, hyz, h ⟩ ) | ( ( ⟨ hyu, rfl, y, hy, z, hz, hyz, h ⟩ | ⟨ rfl, y, hy, z, hz, hyz, h ⟩ ) | ( ⟨ hwu, rfl, y, hy, z, hz, hyz, h ⟩ | ⟨ hwv, rfl, y, hy, z, hz, hyz, h ⟩ ) ) ) <;> simp_all ( config := { decide := Bool.true } ) [ Sym2.eq ] ;
          grind +ring;
          · grind +ring;
          · grind +ring;
          · exact ⟨ y, z, ⟨ hy, hz, hyz ⟩, h ⟩;
          · grind +ring;
          · grind +ring;
        -- Since $t2$ contains $\{v,w\}$, we can write $t2 = \{v,w,x\}$ for some $x$.
        obtain ⟨x, hx⟩ : ∃ x : V, t2 = {v, w, x} := by
          norm_num +zetaDelta at *;
          have := Finset.card_eq_three.mp ht2.2; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
          unfold triangleEdges at *; simp_all +decide [ Sym2.eq_swap ] ;
          grind;
        -- Since $\{v,w\}$ is not a cover (otherwise $\tau(G) \le 1$), there exists a triangle $t_3$ that does not contain the edge $\{v,w\}$.
        obtain ⟨t3, ht3, ht3_not_vw⟩ : ∃ t3 : Finset V, t3 ∈ G.cliqueFinset 3 ∧ Sym2.mk (v, w) ∉ triangleEdges t3 := by
          by_contra h_contra;
          -- If no such triangle $t3$ exists, then $\{v,w\}$ is a cover, contradicting $\tau(G) > 1$.
          have h_cover : IsTriangleCovering G {Sym2.mk (v, w)} := by
            unfold IsTriangleCovering; aesop;
            intro t ht; specialize h_contra t; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            simp_all +decide [ SimpleGraph.isClique_iff, triangleEdges ];
            simp_all +decide [ SimpleGraph.deleteEdges, Set.Pairwise ];
            grind +ring;
          have h_cover_card : triangleCoveringNumber G ≤ 1 := by
            unfold triangleCoveringNumber; aesop;
            have h_cover_card : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ 1 := by
              refine' Finset.min_le _;
              simp +zetaDelta at *;
              exact ⟨ { s(v, w) }, ⟨ by aesop_cat, h_cover ⟩, by aesop_cat ⟩;
            cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
          linarith;
        simp_all +decide [ triangleEdges ];
        -- By `third_triangle_forces_k4`, $t_3$ must be $\{u,v,x\}$ or $\{u,w,x\}$.
        have h_t3_cases : t3 = {u, v, x} ∨ t3 = {u, w, x} := by
          apply third_triangle_forces_k4 G u v w x ⟨ by
            tauto, by
            tauto, by
            grind, by
            tauto, by
            rintro rfl; simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_singleton ] at ht2 <;> aesop, by
            rintro rfl; simp_all +decide [ SimpleGraph.isNClique_iff ] ; ⟩ (by
          simp_all +decide [ SimpleGraph.isNClique_iff ]) (by
          simp_all +decide [ SimpleGraph.isNClique_iff ]) h_nu_1 t3 (by
          exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ht3 ⟩) (by
          simp_all +decide [ triangleEdges ];
          exact ht3_not_vw);
        rcases h_t3_cases with ( rfl | rfl ) <;> simp_all ( config := { decide := Bool.true } ) [ SimpleGraph.isNClique_iff ];
        · use u, v, huv, w, huw, x;
          by_cases hu : u = x <;> by_cases hv : v = x <;> by_cases hw : w = x <;> simp_all ( config := { decide := Bool.true } );
        · use u, v, huv, w, by tauto, x, by
            rintro rfl; simp_all ( config := { decide := Bool.true } ) ;
            rw [ Finset.card_insert_of_not_mem, Finset.card_singleton ] at ht3 <;> aesop;
          grind

end AristotleLemmas

theorem tuza_conjecture_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu_1 : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  -- The full proof follows from iteration 2's exists_triangles_for_k4_of_tau_gt_2
  -- combined with k4_implies_tau_le_2_if_nu_1
  -- For Aristotle to complete
  by_cases h_tau_gt_1 : triangleCoveringNumber G > 1;
  · obtain ⟨ u, v, w, x, h_distinct, h_edges, h_nu_1 ⟩ := exists_k4_of_nu_1_and_tau_gt_1 G h_nu_1 h_tau_gt_1;
    apply k4_implies_tau_le_2_if_nu_1 G u v w x ⟨ h_distinct, h_edges, h_nu_1.1, h_nu_1.2.1, h_nu_1.2.2.1, h_nu_1.2.2.2.1 ⟩ ⟨ h_nu_1.2.2.2.2.1, h_nu_1.2.2.2.2.2.1, h_nu_1.2.2.2.2.2.2.1, h_nu_1.2.2.2.2.2.2.2.1, h_nu_1.2.2.2.2.2.2.2.2.1, h_nu_1.2.2.2.2.2.2.2.2.2 ⟩ ‹_›;
  · grind

end