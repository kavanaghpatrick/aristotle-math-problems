import Mathlib

-- Try N=200
theorem erdos_324_bounded_200 :
    ∀ a b c d : Fin 200, a < b → c < d →
      a.val ^ 5 + b.val ^ 5 = c.val ^ 5 + d.val ^ 5 → a = c ∧ b = d := by
  native_decide
