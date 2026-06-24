import Mathlib

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

/--
Harborth-Piepmeyer 9-point configuration witness for Erdős problem 100.

There exists a 9-point set A ⊂ ℝ² with the property that any two distinct
pairwise distances differ by at least 1, and the diameter of A is strictly
less than 5. Published by Harborth and Piepmeyer in "Three distinct
distances in the plane", Geom. Dedicata 61 (1996) 315–327.

Status: OPEN - the explicit construction from the paper has not yet been
formalized. The construction requires finding 9 specific points in ℝ² where
all pairwise distances come from a set of at most 4 values that are pairwise
≥ 1 apart, with the maximum < 5.
-/
theorem erdos_100_piepmeyer :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 9 ∧
      (∀ p₁ q₁ p₂ q₂,
        p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
        dist p₁ q₁ ≠ dist p₂ q₂ → |dist p₁ q₁ - dist p₂ q₂| ≥ 1) ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) < 5 := by
  sorry

end
