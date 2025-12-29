/-
`slot86` stores a backup presentation of the cycle-of-four argument that phrases the
local covering choices as explicit `S_e` witnesses.  Each `S_e` represents at most two
edges drawn from `M_edges_at` that cover all triangles through one shared vertex.
If the four witnesses exist, their union certifies a global cover of size ≤ 8.
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Standard triangle-packing infrastructure. -/
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

def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- 4-cycle definition. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- `SeWitness` packages the data we previously obtained from `local_cover_le_2`. -/
structure SeWitness (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Prop where
  edges : Finset (Sym2 V)
  card_le : edges.card ≤ 2
  subset : edges ⊆ M_edges_at G M v
  covers : ∀ t ∈ G.cliqueFinset 3, v ∈ t →
    (∃ e ∈ M_edges_at G M v, e ∈ t.sym2) →
    (∃ e ∈ edges, e ∈ t.sym2)

/-- Alternative target: assuming the four `S_e` witnesses exist, the tau bound follows.
    Aristotle should either construct these witnesses explicitly or show how the
    slot73 argument instantiates them. -/
theorem tau_le_8_cycle4_via_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (h_only_ab : ∀ Z ∈ M, v_ab ∈ Z → Z = A ∨ Z = B)
    (h_only_bc : ∀ Z ∈ M, v_bc ∈ Z → Z = B ∨ Z = C)
    (h_only_cd : ∀ Z ∈ M, v_cd ∈ Z → Z = C ∨ Z = D)
    (h_only_da : ∀ Z ∈ M, v_da ∈ Z → Z = D ∨ Z = A)
    (Se_ab : SeWitness G M v_ab) (Se_bc : SeWitness G M v_bc)
    (Se_cd : SeWitness G M v_cd) (Se_da : SeWitness G M v_da)
    (h_triangles : ∀ t ∈ G.cliqueFinset 3,
        v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Aristotle follows the S_e union strategy here.
  sorry
