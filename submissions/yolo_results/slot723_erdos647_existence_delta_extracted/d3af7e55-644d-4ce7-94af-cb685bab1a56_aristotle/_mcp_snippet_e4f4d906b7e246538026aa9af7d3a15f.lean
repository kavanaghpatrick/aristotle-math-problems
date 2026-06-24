import Mathlib
open ArithmeticFunction

-- Test: can we handle 5000?
set_option maxHeartbeats 4000000 in
example : ∀ n : Fin 5000, (n : ℕ) ≤ 24 ∨ ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
  native_decide