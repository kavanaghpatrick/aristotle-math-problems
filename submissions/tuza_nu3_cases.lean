/-
Tuza's Conjecture for ν ≤ 3: Case-by-Case Approach
Prove each case (ν=0,1,2,3) individually, then combine.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option linter.mathlibStandardSet false

open scoped BigOperators Classical Pointwise

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- Case ν = 0: No triangles, so τ = 0
theorem tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  sorry

-- Case ν = 1: Single packing triangle, τ ≤ 2
-- All triangles share a vertex with the packing triangle
-- They form an intersecting family → star or K4 → τ ≤ 2
theorem tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

-- Case ν = 2: Two packing triangles, τ ≤ 4
theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

-- Case ν = 3: Three packing triangles, τ ≤ 6
theorem tuza_case_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 3) : triangleCoveringNumber G ≤ 6 := by
  sorry

-- Main theorem: combine cases
theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt2 | heq2
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt2) with hlt3 | heq3
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt3) with hlt4 | heq4
        · omega
        · simp only [heq4, mul_zero]; exact (tuza_case_nu_0 G heq4).le
      · simp only [heq3, mul_one]; exact tuza_case_nu_1 G heq3
    · simp only [heq2]; norm_num; exact tuza_case_nu_2 G heq2
  · simp only [heq]; norm_num; exact tuza_case_nu_3 G heq

end
