/-
Tuza ν=2: Assembly using proven lemmas

We have PROVEN (in context):
- tau_S_le_2: τ(S_e) ≤ 2
- lemma_2_2: S_e triangles pairwise share edges
- lemma_2_3: ν(G \ T_e) = ν - 1
- tuza_case_nu_0: ν = 0 → τ = 0

For ν = 2: Use τ(G) ≤ τ(S_e) + τ(S_f) + τ(X) where X = T_e ∩ T_f
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

theorem tuza_nu1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) : triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end
