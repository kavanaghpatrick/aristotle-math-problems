import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

theorem erdos_319_c6_lb :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 6 ∧ A.card = 4 ∧
      ∃ δ : ℕ → ℤˣ,
        (∑ n ∈ A, (δ n : ℚ) / n = 0) ∧
        (∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) := by
          by_contra h_contra;
          simp_all +decide [ Finset.ssubset_def ];
          specialize h_contra { 1, 2, 3, 6 } ; simp_all +decide;
          specialize h_contra ( fun n => if n = 1 then -1 else 1 ) ; norm_num at h_contra;
          revert h_contra;
          native_decide +revert