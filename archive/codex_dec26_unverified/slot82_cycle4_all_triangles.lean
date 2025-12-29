/-
`slot82` focuses on the structural component of the cycle-of-four argument:
prove that every triangle of the ambient graph must pass through one of the
four shared vertices of the packing cycle.  The file is fully self-contained,
so Aristotle can reason in isolation.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Standard definition of triangle packings. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- Triangle packing number by direct enumeration. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G)
    |>.image Finset.card |>.max |>.getD 0

/-- Maximal triangle packings. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- Triangle sets containing a specific vertex. -/
def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => v ∈ t

/-- Definition of a 4-cycle of triangles with empty diagonals. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- Target lemma: any triangle in the graph must contain one of the four shared vertices
    of the cycle configuration.  The empty-diagonal hypotheses force each triangle to
    pass through a shared vertex, otherwise we could augment the packing. -/
lemma cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t := by
  -- Aristotle reinstates the slot73 argument here.
  sorry
