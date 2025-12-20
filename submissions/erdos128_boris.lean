import Mathlib

variable {V : Type*} {G : SimpleGraph V} [Fintype V]

theorem erdos_128 :
    (∀ V' : Set V,
      2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) → ¬ G.CliqueFree 3 := by
  sorry
