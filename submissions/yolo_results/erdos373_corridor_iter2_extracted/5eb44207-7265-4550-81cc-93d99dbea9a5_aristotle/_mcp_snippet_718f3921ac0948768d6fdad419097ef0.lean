import Mathlib

-- Try 500
set_option maxHeartbeats 8000000 in
theorem test_500 : ∀ a ∈ Finset.Icc 3 500, ∀ n ∈ Finset.Icc (a + 2) (2 * a - 1),
    ∀ b ∈ Finset.Icc 2 a, n.factorial = a.factorial * b.factorial → (n = 10 ∧ a = 7 ∧ b = 6) := by
  native_decide
