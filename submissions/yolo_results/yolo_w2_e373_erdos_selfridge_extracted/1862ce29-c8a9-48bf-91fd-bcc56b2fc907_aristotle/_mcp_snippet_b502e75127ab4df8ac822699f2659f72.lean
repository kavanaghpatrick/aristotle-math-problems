import Mathlib

-- Let's try a = 500
set_option maxRecDepth 8000 in
example : ∀ a ∈ Finset.range 501, ∀ n ∈ Finset.range 1001, ∀ b ∈ Finset.range 501,
    (n.factorial = a.factorial * b.factorial ∧ 1 < n ∧ 1 < a ∧ 1 < b ∧ b ≤ a ∧ a + 1 ≠ n) →
    (n, a, b) = (10, 7, 6) := by native_decide
