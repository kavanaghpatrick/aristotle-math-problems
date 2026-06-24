import Mathlib

/-
**Erdős 124 — Step-M completeness criterion (Cassels filling).**

If the `M` consecutive integers `T+1, …, T+M` all lie in `R` (the window condition
`hwin`), and `R` is closed under adding `M` above `T` (the closure condition `hclose`),
then `R` contains every integer beyond `T`.
-/
theorem erdos124_step_completeness
    (R : Set ℕ) (M T : ℕ) (hM : 0 < M)
    (hwin : ∀ i, i < M → (T + 1 + i) ∈ R)
    (hclose : ∀ n, T < n → n ∈ R → (n + M) ∈ R) :
    ∀ n, T < n → n ∈ R := by
  intro n hn;
  induction' n using Nat.strong_induction_on with n ih;
  by_cases h_case : n ≤ T + M;
  · convert hwin ( n - T - 1 ) _ using 1 <;> omega;
  · exact hclose ( n - M ) ( by omega ) ( ih _ ( by omega ) ( by omega ) ) |> fun h => by convert h using 1; omega;