import Mathlib

-- Try 250
set_option maxRecDepth 8000 in
theorem bounded_250 :
    ∀ a ∈ Finset.range 251, ∀ n ∈ Finset.Ico (a + 2) (2 * a),
    ∀ b ∈ Finset.Ico 2 (a + 1),
    n.factorial = a.factorial * b.factorial → (n, a, b) = (10, 7, 6) := by
  native_decide
