import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.ZMod.Basic

theorem test_theorem_1 : 1 + 1 = 2 := by omega

theorem test_theorem_2 (n : ℕ) (hn : n > 0) : n ≥ 1 := by omega

lemma helper_lemma : ∀ n : ℕ, 0 ≤ n := by
  intro n
  exact Nat.zero_le n

def test_constant : ℕ := 42
