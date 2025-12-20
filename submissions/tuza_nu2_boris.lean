import Mathlib

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter (fun S =>
    S ⊆ G.cliqueFinset 3 ∧
    (S : Set (Finset V)).Pairwise (fun t1 t2 => (t1 ∩ t2).card ≤ 1))).image Finset.card |>.max |>.getD 0

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2)).image Finset.card |>.min |>.getD 0

theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) : triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end
