/-
`slot80` is the master scaffolding file for the ν = 4 cycle-of-four argument.
It mirrors the trusted slot73 derivation but stays entirely self-contained so that
Aristotle can rebuild the proof inside this single submission.

We restate every definition needed by the final inequality `tau_le_8_cycle4` and we
package the three crucial helper lemmas as axioms.  Aristotle is expected to
re-prove those lemmas while filling in the `sorry` below.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A triangle packing is a subset of `G.cliqueFinset 3` with pairwise intersections of
    size at most one. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- Cardinality of a maximum triangle packing, defined by brute-force search. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G)
    |>.image Finset.card |>.max |>.getD 0

/-- Maximum triangle packings have the required packing property and achieve
    `trianglePackingNumber`. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- Triangle covering number restricted to a supplied triangle set. -/
noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset
    |>.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

/-- Triangles sharing an edge with `t`. -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun x => (x ∩ t).card ≥ 2

/-- Triangles containing a vertex `v`. -/
def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => v ∈ t

/-- All edges of packing triangles that touch `v`. -/
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- Literal definition of a 4-cycle of triangles.  The diagonals `(A ∩ C)` and `(B ∩ D)`
    are empty so every shared vertex lies on exactly two neighboring triangles. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- Proven in slot73: each shared vertex admits a local cover of size ≤ 2 consisting of
    edges from its incident packing triangles. -/
axiom local_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ M_edges_at G M v ∧
    ∀ t ∈ G.cliqueFinset 3, v ∈ t →
      (∃ e ∈ M_edges_at G M v, e ∈ t.sym2) →
      (∃ e ∈ E', e ∈ t.sym2)

/-- Proven in slot73: all triangles touch one of the four shared vertices. -/
axiom cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t

/-- Proven in slot73: triangles that share an edge with a packing triangle have a
    supporting edge in `M_edges_at` through any shared vertex. -/
axiom cycle4_triangle_at_vertex_supported (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (hA : A ∈ M)
    (v : V) (hv : v ∈ A)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G A) (hvt : v ∈ t) :
    ∃ e ∈ M_edges_at G M v, e ∈ t.sym2

/-- Main target: covering every triangle of `G` with at most eight edges in the 4-cycle
    configuration.  Step outline:
    1. apply `local_cover_le_2` to the four shared vertices;
    2. take the union of the resulting edge sets (size ≤ 8);
    3. use `cycle4_all_triangles_contain_shared` to pick a vertex and
       `cycle4_triangle_at_vertex_supported` to extract the covering edge. -/
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
  -- Aristotle inserts the slot73 reasoning here.
  sorry
