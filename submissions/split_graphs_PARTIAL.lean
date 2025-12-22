/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cd3636f6-782a-423a-b33f-d1ff3301c00a

The following was proved by Aristotle:

- lemma split_triangle_has_two_in_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (K I : Finset V) (h_split : isSplitGraph G K I)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (t ∩ K).card ≥ 2

- lemma split_same_clique_edge_share (G : SimpleGraph V) [DecidableRel G.Adj]
    (K I : Finset V) (h_split : isSplitGraph G K I)
    (e : Finset V) (he_edge : e.card = 2) (he_clique : e ⊆ K)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (he1 : e ⊆ t1) (he2 : e ⊆ t2) :
    (t1 ∩ t2).card ≥ 2

- lemma split_clique_edges_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (K I : Finset V) (h_split : isSplitGraph G K I) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ K.powersetCard 2, ∀ v ∈ e, v ∈ t
-/

/-
Tuza's Conjecture for Split Graphs

FRONTIER: General split graphs are OPEN. Only threshold subclass proven (Botler et al. 2021).

DEFINITION: A split graph G = (K ∪ I, E) has:
- K: a clique (all pairs adjacent)
- I: an independent set (no pairs adjacent)
- K ∩ I = ∅ and K ∪ I = V

KEY STRUCTURAL INSIGHT: Every triangle in a split graph has ≥2 vertices in K.
Proof: Triangles need 3 mutually adjacent vertices. I is independent, so ≤1 in I.

WHY TRACTABLE: Our proven lemmas apply directly:
- structural_cover: pairwise sharing triangles have τ ≤ 2
- intersecting_triangles_structure: pairwise sharing → star OR K4
- k4_cover: triangles on ≤4 vertices have τ ≤ 2

ATTACK: Induction on |K|, using that clique structure controls all triangles.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Standard definitions from our proven infrastructure

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

-- Split graph definition

def isSplitGraph (G : SimpleGraph V) [DecidableRel G.Adj] (K I : Finset V) : Prop :=
  (∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) ∧  -- K is clique
  (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) ∧          -- I is independent
  Disjoint K I ∧                             -- disjoint
  K ∪ I = Finset.univ

-- partition

-- Key structural lemma: triangles use ≥2 clique vertices
lemma split_triangle_has_two_in_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (K I : Finset V) (h_split : isSplitGraph G K I)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (t ∩ K).card ≥ 2 := by
  simp_all +decide [ Finset.mem_filter, SimpleGraph.isClique_iff, Finset.card_eq_three ];
  have := h_split.2.1;
  rcases Finset.card_eq_three.mp ht.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ];
  -- Since $K$ and $I$ are disjoint and their union is the entire set of vertices, each vertex must be in either $K$ or $I$.
  have h_partition : ∀ x, x ∈ K ∨ x ∈ I := by
    exact fun x => Finset.mem_union.mp ( h_split.2.2.2.symm ▸ Finset.mem_univ x );
  grind

-- Triangles sharing same clique edge share that edge
lemma split_same_clique_edge_share (G : SimpleGraph V) [DecidableRel G.Adj]
    (K I : Finset V) (h_split : isSplitGraph G K I)
    (e : Finset V) (he_edge : e.card = 2) (he_clique : e ⊆ K)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (he1 : e ⊆ t1) (he2 : e ⊆ t2) :
    (t1 ∩ t2).card ≥ 2 := by
  exact le_trans he_edge.ge ( Finset.card_le_card fun x hx => by aesop )

-- Clique edges cover all triangles
lemma split_clique_edges_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (K I : Finset V) (h_split : isSplitGraph G K I) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ K.powersetCard 2, ∀ v ∈ e, v ∈ t := by
  intro t ht
  have h_triangle_has_two_in_K : (t ∩ K).card ≥ 2 := by
    exact?;
  obtain ⟨ e, he ⟩ := Finset.exists_subset_card_eq h_triangle_has_two_in_K;
  use e;
  grind

/- Aristotle failed to find a proof. -/
-- MAIN THEOREM: Tuza for split graphs
theorem tuza_split_graphs (G : SimpleGraph V) [DecidableRel G.Adj]
    (K I : Finset V) (h_split : isSplitGraph G K I) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end