/-
`slot85` repeats the main `tau_le_8_cycle4` statement but requests a single inline proof.
Aristotle should organize the argument exactly as in slot73 yet without outsourcing the
work to standalone lemmas.  That means re-deriving the local cover bounds, the shared
vertex property, and the supporting-edge argument directly inside the proof below.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangle packings. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- Triangle packing number. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G)
    |>.image Finset.card |>.max |>.getD 0

/-- Maximal packings. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- Triangle covering number on arbitrary triangle families. -/
noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset
    |>.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

/-- Local triangle collections and edge sets used in the inline proof. -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun x => (x ∩ t).card ≥ 2

def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- Four-cycle definition. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- Main target with inline proof placeholder.  Aristotle should execute the three-step
    plan entirely inside this proof without appealing to external lemmas. -/
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
  -- Inline recreation of the slot73 strategy goes here.
  sorry
