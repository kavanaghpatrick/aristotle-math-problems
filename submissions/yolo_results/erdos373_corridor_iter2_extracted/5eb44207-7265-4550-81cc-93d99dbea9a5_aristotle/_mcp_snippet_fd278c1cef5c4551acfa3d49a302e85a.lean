import Mathlib

-- Reformulate using product to avoid computing full factorials
-- For a > 200, we need: (a+1)*...*(n) ≠ b! for all valid (n, b)
-- This is equivalent since n! = a! * b! ↔ n!/a! = b! ↔ ∏_{i=a+1}^{n} i = b!

set_option maxHeartbeats 16000000 in
lemma finite_check_201_1000 :
    ∀ a ∈ Finset.Icc 201 1000, ∀ n ∈ Finset.Icc (a + 2) (2 * a - 1),
    ∀ b ∈ Finset.Icc 2 a,
    (Finset.Icc (a + 1) n).prod id ≠ b.factorial := by
  native_decide
