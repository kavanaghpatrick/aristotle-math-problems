/-
`slot89` packages the same `tau_le_8_cycle4` inequality but leaves the argument in a
heavily commented informal style.  Aristotle should translate each bullet back into Lean
when formalizing the final submission.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Foundational definitions so the file is standalone. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G)
    |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset
    |>.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

/-- Triangles sharing an edge with a fixed triangle. -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun x => (x ∩ t).card ≥ 2

def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- Informal target: state the tau bound with explicit hints on how to complete the proof. -/
theorem tau_le_8_cycle4_informal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (h_only_ab : ∀ Z ∈ M, v_ab ∈ Z → Z = A ∨ Z = B)
    (h_only_bc : ∀ Z ∈ M, v_bc ∈ Z → Z = B ∨ Z = C)
    (h_only_cd : ∀ Z ∈ M, v_cd ∈ Z → Z = C ∨ Z = D)
    (h_only_da : ∀ Z ∈ M, v_da ∈ Z → Z = D ∨ Z = A)
    (h_triangles : ∀ t ∈ G.cliqueFinset 3,
        v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t)
    (support : ∀ (X : Finset V) (hX : X ∈ M)
        (v ∈ X) {t : Finset V}, t ∈ trianglesSharingEdge G X → v ∈ t →
        ∃ e ∈ M_edges_at G M v, e ∈ t.sym2)
    (local_covers : ∀ v, v ∈ {v_ab, v_bc, v_cd, v_da} →
        ∃ E', E'.card ≤ 2 ∧ E' ⊆ M_edges_at G M v ∧
          ∀ t ∈ G.cliqueFinset 3, v ∈ t →
            (∃ e ∈ M_edges_at G M v, e ∈ t.sym2) →
            (∃ e ∈ E', e ∈ t.sym2)) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Outline:
  -- * unpack the four `local_covers` witnesses as explicit `S_e` sets;
  -- * take their union to obtain at most eight edges;
  -- * use `h_triangles` to select a shared vertex for any triangle;
  -- * use `support` to route the triangle to the relevant `S_e` edge.
  sorry
