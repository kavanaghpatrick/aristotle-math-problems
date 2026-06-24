import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

theorem erdos_319_c_N_7_to_10_lb :
    ∀ N ∈ ({7, 8, 9, 10} : Finset ℕ),
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = 4 ∧
        ∃ δ : ℕ → ℤˣ,
          (∑ n ∈ A, (δ n : ℚ) / n = 0) ∧
          (∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) := by
  intro N hN
  use {1, 2, 3, 6};
  refine' ⟨ _, _, _ ⟩ <;> norm_num [ Finset.subset_iff ];
  · fin_cases hN <;> trivial;
  · refine' ⟨ fun n => if n = 1 then -1 else 1, _, _ ⟩ <;> simp +decide [ Finset.ssubset_def ];
    · norm_num;
    · native_decide +revert