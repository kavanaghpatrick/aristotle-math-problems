import Mathlib

open Finset Nat

/-!
# Erdős 1003: Fixed-support finiteness for φ(n) = φ(n+1)

For any finite set S of primes, only finitely many positive integers n
satisfy φ(n) = φ(n+1) with supp(n) ∪ supp(n+1) ⊆ S.

## Proof outline

The map `n ↦ (S.filter (· ∣ n), S.filter (· ∣ (n+1)))` is an injection from
our set into `S.powerset × S.powerset` (finite). Injectivity follows because
`φ(n)/n = ∏_{p|n} (1 - 1/p)` depends only on the prime support of `n`, so
if two solutions share the same prime supports, simple algebra forces them equal.
-/

/-
The identity `φ(n) * rad(n) = n * ∏_{p | n} (p - 1)` where `rad(n) = ∏ p` over prime factors.
-/
lemma totient_mul_rad_eq (n : ℕ) :
    n.totient * n.primeFactors.prod id = n * n.primeFactors.prod (· - 1) := by
  rw [ Nat.totient_eq_div_primeFactors_mul ];
  simp +decide [mul_comm];
  rw [ ← mul_assoc, Nat.mul_div_cancel' ( Nat.prod_primeFactors_dvd _ ) ]

/-
If two positive integers share the same set of prime factors, then `φ(n₁) * n₂ = φ(n₂) * n₁`.
This encodes the fact that `φ(n)/n` depends only on the prime support.
-/
lemma totient_ratio_of_primeFactors_eq {n₁ n₂ : ℕ}
    (h : n₁.primeFactors = n₂.primeFactors) :
    n₁.totient * n₂ = n₂.totient * n₁ := by
  have h1 := totient_mul_rad_eq n₁
  have h2 := totient_mul_rad_eq n₂
  rw [h] at h1
  nlinarith [Finset.prod_pos (s := n₂.primeFactors) (f := id)
    (fun p hp => Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))]

/-
Auxiliary: the filter of S by divisibility gives the prime factors when support is in S.
-/
lemma primeFactors_eq_filter_of_support_subset {n : ℕ} {S : Finset ℕ} (hn : n ≠ 0)
    (hS : ∀ p ∈ S, p.Prime) (hsupp : ∀ p, p.Prime → p ∣ n → p ∈ S) :
    n.primeFactors = S.filter (· ∣ n) := by
  ext; aesop;

/-
For `n > 0`, the prime factors of `n` as elements of `S` determine `n` uniquely
among solutions of `φ(n) = φ(n+1)` with support in `S`.
-/
theorem erdos_1003_fixed_support_finite (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    {n : ℕ | 0 < n ∧ Nat.totient n = Nat.totient (n + 1) ∧
             (∀ p, p.Prime → p ∣ n → p ∈ S) ∧
             (∀ p, p.Prime → p ∣ (n + 1) → p ∈ S)}.Finite := by
  --Map each solution to a pair of its prime divisors. This map is injective.
  set f : ℕ → Finset ℕ × Finset ℕ := fun n => (S.filter (· ∣ n), S.filter (· ∣ (n + 1))) with hf_def
  have h_mapsTo : {n : ℕ | 0 < n ∧ n.totient = (n + 1).totient ∧ (∀ p, p.Prime → p ∣ n → p ∈ S) ∧ (∀ p, p.Prime → p ∣ (n + 1) → p ∈ S)} ⊆ f ⁻¹' (S.powerset ×ˢ S.powerset) := by
    exact fun n hn => ⟨ Finset.mem_powerset.mpr <| Finset.filter_subset _ _, Finset.mem_powerset.mpr <| Finset.filter_subset _ _ ⟩;
  apply Set.Finite.of_finite_image;
  any_goals exact f;
  · exact Set.Finite.subset ( Set.toFinite _ ) ( Set.image_subset_iff.mpr h_mapsTo );
  · intro n hn m hm hnm
    simp [hf_def] at hnm
    have h_eq : n.primeFactors = m.primeFactors := by
      rw [ primeFactors_eq_filter_of_support_subset hn.1.ne' hS hn.2.2.1, primeFactors_eq_filter_of_support_subset hm.1.ne' hS hm.2.2.1, hnm.1 ]
    have h_eq' : (n + 1).primeFactors = (m + 1).primeFactors := by
      grind
    have h_eq'' : n.totient * (m + 1) = m.totient * (n + 1) := by
      have h := totient_ratio_of_primeFactors_eq h_eq'
      rw [← hn.2.1, ← hm.2.1] at h; exact h
    have h_eq''' : n = m := by
      have h_eq''' : n.totient * m = m.totient * n := by
        exact totient_ratio_of_primeFactors_eq h_eq
      nlinarith [ Nat.totient_pos.2 hn.1, Nat.totient_pos.2 hm.1 ]
    exact h_eq'''