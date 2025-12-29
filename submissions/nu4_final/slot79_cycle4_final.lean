/-
Self-contained scaffolding file for the cycle-of-four case in the ν = 4 Tuza project.
The goal is to expose the exact lemmas Aristotle needs, mirroring the previous slot73
output but keeping this file completely standalone (no imports from `proven/`).

The overall proof strategy that Aristotle should fill in is the same three-step plan
outlined by the user:
1. The "diagonal" constraint guarantees that every shared vertex of the 4-cycle is
   contained in exactly two packing elements.  This hypothesis allows an application
   of `local_cover_le_2`, which extracts at most two supporting edges per shared vertex.
2. Applying `local_cover_le_2` at the four shared vertices produces at most eight edges
   total.  These edges are subsets of the `M_edges_at` structures and therefore lie in
   the original graph.
3. The lemmas `cycle4_all_triangles_contain_shared` and
   `cycle4_triangle_at_vertex_supported` ensure that every triangle of the graph passes
   through one of the four shared vertices, and whenever a triangle passes through such
   a vertex we can cover it by the edges gathered in Step 2.

The theorem `tau_le_8_cycle4` is left as `sorry` so Aristotle can reproduce the proven
argument using the lemmas provided below.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A `Finset` of triangles is a triangle packing if it sits inside `G.cliqueFinset 3`
    and every pair of distinct triangles shares at most one vertex. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- The maximum size of a triangle packing, defined via a brute-force search over all
    subsets of `G.cliqueFinset 3`. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G)
    |>.image Finset.card |>.max |>.getD 0

/-- `M` is a maximum triangle packing if it is a packing whose cardinality realizes the
    `trianglePackingNumber`. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- The local triangle covering number for an arbitrary collection of triangles. -/
noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset
    |>.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

/-- Auxiliary collections of triangles used by the cycle lemmas. -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun x => (x ∩ t).card ≥ 2

/-- All triangles that contain a specific vertex. -/
def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => v ∈ t

/-- `M_edges_at G M v` lists all edges inside the triangles of `M` that are incident to `v`. -/
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- A simple cycle of four triangles: the packing is literally `{A, B, C, D}` with
    alternating intersections of size one and diagonals disjoint. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- Local covering bound used four times in the main proof.  The idea is that if a vertex
    `v` belongs to exactly two triangles of the maximum packing (say `A` and `B`), then
    there is a subset of at most two edges inside `M_edges_at G M v` covering every
    triangle containing `v` that also receives support from `M`. -/
lemma local_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ M_edges_at G M v ∧
    ∀ t ∈ G.cliqueFinset 3, v ∈ t →
      (∃ e ∈ M_edges_at G M v, e ∈ t.sym2) →
      (∃ e ∈ E', e ∈ t.sym2) := by
  -- Proven in slot73: every supported triangle through `v` is covered by ≤ 2 local edges.
  sorry

/-- Structural lemma: every triangle in the graph meets one of the four shared vertices of
    the cycle.  This relies on the maximality of the packing and the cycle structure. -/
lemma cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t := by
  -- Proven in slot73: cycle-of-four packings force every triangle to touch a shared vertex.
  sorry

/-- Support lemma: whenever a triangle shares an edge with a packing element and passes
    through a vertex `v` of that element, there is a supporting edge in `M_edges_at` that
    lies inside the triangle. -/
lemma cycle4_triangle_at_vertex_supported (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (hA : A ∈ M)
    (v : V) (hv : v ∈ A)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G A) (hvt : v ∈ t) :
    ∃ e ∈ M_edges_at G M v, e ∈ t.sym2 := by
  -- Proven in slot73: triangles sharing an edge with `A` contain a supporting edge at `v`.
  sorry

/-- Final statement: in the cycle-of-four configuration, the triangle covering number of
    the entire graph is at most eight.  Aristotle should combine the three proven facts:
    `local_cover_le_2` supplies ≤2 edges per shared vertex, the cycle lemmas show every
    triangle contains some shared vertex, and the supporting edges ensure those local
    collections actually hit the triangle. -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (h_only_ab : ∀ Z ∈ M, v_ab ∈ Z → Z = A ∨ Z = B)
    (h_only_bc : ∀ Z ∈ M, v_bc ∈ Z → Z = B ∨ Z = C)
    (h_only_cd : ∀ Z ∈ M, v_cd ∈ Z → Z = C ∨ Z = D)
    (h_only_da : ∀ Z ∈ M, v_da ∈ Z → Z = D ∨ Z = A) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Step 1: apply `local_cover_le_2` to each shared vertex using the diagonal constraints.
  -- Step 2: union the four resulting edge sets, giving at most eight edges in total.
  -- Step 3: cover any triangle via `cycle4_all_triangles_contain_shared` and
  --         `cycle4_triangle_at_vertex_supported`.
  sorry
