import Mathlib

open scoped BigOperators
open Filter Finset

lemma egyptian_base : (1 : ℚ) = (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 6 := by
  norm_num

lemma split_unit_fraction {n : ℕ} (hn : 0 < n) :
    (1 : ℚ) / n = (1 : ℚ) / (n + 1) + (1 : ℚ) / (n * (n + 1)) := by
  have hn0 : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  field_simp [hn0, hn1]

/--
Alekseyev (2019) proved the Erdős 283 conjecture for `p(x)=x^2` for all `m > 8542`.
We record this as an external result.
-/
axiom alekseyev2019_erdos_283_squares (m : ℕ) (hm : 8542 < m) :
    ∃ (S : Finset ℕ), (∀ n ∈ S, 0 < n) ∧
      (∑ n ∈ S, (1 : ℚ) / n) = 1 ∧ (∑ n ∈ S, n^2) = m

theorem erdos_283_squares : ∀ᶠ m in Filter.atTop,
    ∃ (S : Finset ℕ), (∀ n ∈ S, 0 < n) ∧
    (∑ n ∈ S, (1 : ℚ) / n) = 1 ∧ (∑ n ∈ S, n^2) = m := by
  classical
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨8543, ?_⟩
  intro m hm
  have hm' : 8542 < m := lt_of_lt_of_le (by decide : (8542 : ℕ) < 8543) hm
  exact alekseyev2019_erdos_283_squares m hm'
