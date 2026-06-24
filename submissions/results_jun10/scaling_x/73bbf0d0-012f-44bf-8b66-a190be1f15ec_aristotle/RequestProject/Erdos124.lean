import Mathlib

open scoped BigOperators
open scoped Classical

namespace Erdos124

/-- The set of sums of distinct powers `d^i` with all exponents `i ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/-
Scaling identity for `sumsOfDistinctPowers`: an integer `x` lies in
`sumsOfDistinctPowers d k` exactly when `d^k` divides `x` and `x / d^k` lies in
`sumsOfDistinctPowers d 0`.
-/
theorem erdos124_scaling (d k x : ℕ) :
    x ∈ Erdos124.sumsOfDistinctPowers d k ↔
      d ^ k ∣ x ∧ (x / d ^ k) ∈ Erdos124.sumsOfDistinctPowers d 0 := by
  refine' ⟨ fun ⟨ s, hs, hs' ⟩ ↦ _, _ ⟩;
  · -- Let's rewrite the sum to prepare for factoring out $d^k$.
    have h_sum : ∑ i ∈ s, d ^ i = d ^ k * ∑ j ∈ s.image (fun i => i - k), d ^ j := by
      rw [ Finset.sum_image ];
      · rw [ Finset.mul_sum _ _ _, Finset.sum_congr rfl ] ; intros ; rw [ ← pow_add, Nat.add_sub_of_le ( hs _ ‹_› ) ];
      · exact fun i hi j hj hij => by linarith [ Nat.sub_add_cancel ( hs i hi ), Nat.sub_add_cancel ( hs j hj ) ] ;
    by_cases h : d ^ k = 0 <;> simp_all +decide;
    · exact ⟨ ∅, by aesop ⟩;
    · exact ⟨ hs'.symm ▸ dvd_mul_right _ _, ⟨ Finset.image ( fun i => i - k ) s, fun i hi => Nat.zero_le _, by rw [ ← hs', Nat.mul_div_cancel_left _ ( Nat.pos_of_ne_zero ( by aesop ) ) ] ⟩ ⟩;
  · rintro ⟨ h₁, s, hs, hs' ⟩;
    refine' ⟨ s.image fun i => i + k, _, _ ⟩ <;> simp_all +decide [ Finset.sum_image, pow_add ];
    rw [ ← Finset.sum_mul _ _ _, hs', Nat.div_mul_cancel h₁ ]

end Erdos124