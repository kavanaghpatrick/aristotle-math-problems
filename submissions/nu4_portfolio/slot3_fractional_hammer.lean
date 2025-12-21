/-
Tuza ν=4 Portfolio - Slot 3: Fractional Hammer

TARGET: Fractional bounds via LP duality
STRATEGY: Formal + Informal - define fractional versions, state as axioms
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

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def fractionalPackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {x : ℝ | ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
    (∀ e ∈ G.edgeFinset, ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1) ∧
    x = (G.cliqueFinset 3).sum w}

noncomputable def fractionalCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf {x : ℝ | ∃ w : Sym2 V → ℝ, (∀ e, 0 ≤ w e) ∧
    (∀ t ∈ G.cliqueFinset 3, (t.sym2).sum w ≥ 1) ∧
    x = G.edgeFinset.sum w}

lemma fractional_duality (G : SimpleGraph V) [DecidableRel G.Adj] :
    fractionalCoveringNumber G = fractionalPackingNumber G := by
  sorry

lemma tau_ge_tau_star (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≥ fractionalCoveringNumber G := by
  sorry

lemma nu_star_ge_nu (G : SimpleGraph V) [DecidableRel G.Adj] :
    fractionalPackingNumber G ≥ (trianglePackingNumber G : ℝ) := by
  sorry

lemma tau_le_2_nu_star (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G := by
  sorry

lemma chapuy_improved_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : fractionalPackingNumber G ≥ 1) :
    (triangleCoveringNumber G : ℝ) ≤
      2 * fractionalPackingNumber G - (1 / Real.sqrt 6) * Real.sqrt (fractionalPackingNumber G) := by
  sorry

theorem tuza_via_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  sorry

end
