import Mathlib

-- Test: can we split the range and combine?
-- Try a = 201 to 400 with Finset
set_option maxHeartbeats 8000000 in
lemma finite_check_201_400 :
    ∀ a ∈ Finset.Icc 201 400, ∀ n ∈ Finset.Icc (a + 2) (2 * a - 1),
    ∀ b ∈ Finset.Icc 2 a, n.factorial = a.factorial * b.factorial →
    (n = 10 ∧ a = 7 ∧ b = 6) := by
  native_decide
