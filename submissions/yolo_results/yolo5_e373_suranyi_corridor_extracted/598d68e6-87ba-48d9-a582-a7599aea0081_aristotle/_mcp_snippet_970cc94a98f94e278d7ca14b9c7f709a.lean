import Mathlib

-- Try 500
example : ∀ a ∈ Finset.Icc 3 500,
    ∀ n ∈ Finset.Icc (a + 2) (2 * a - 1),
      ∀ b ∈ Finset.Icc 2 a,
        Nat.factorial n = Nat.factorial a * Nat.factorial b → 
        n = 10 ∧ a = 7 ∧ b = 6 := by native_decide
