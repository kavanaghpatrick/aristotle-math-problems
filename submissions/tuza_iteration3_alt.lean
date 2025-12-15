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
theorem tuza_conjecture_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu_1 : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  -- The full proof follows from iteration 2's exists_triangles_for_k4_of_tau_gt_2
  -- combined with k4_implies_tau_le_2_if_nu_1
  -- For Aristotle to complete
  sorry

end
