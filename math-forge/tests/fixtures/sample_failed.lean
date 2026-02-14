import Mathlib.Data.Nat.Basic

theorem failed_theorem_1 : ∀ n : ℕ, n > 0 → n * n > n := by
  sorry

theorem failed_theorem_2 (p : ℕ) (hp : Nat.Prime p) : p ≥ 2 := by
  exact hp.two_le

lemma sorry_lemma : False := by
  sorry

theorem another_sorry : 1 = 2 := by
  sorry
