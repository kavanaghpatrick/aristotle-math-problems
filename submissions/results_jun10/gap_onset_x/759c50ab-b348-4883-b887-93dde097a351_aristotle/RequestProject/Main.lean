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

set_option grind.warning false

/-
Per-base bound. For a base `d ≥ 2`, the sum of the merged atoms `d^j` with `k ≤ j ≤ N`
equals `(d^(N+1) - d^k)/(d-1)`, and since `m ≤ d^(N+1)` this is at least
`m/(d-1) - d^k/(d-1)`.
-/
lemma per_base_bound (d : ℕ) (hd : 2 ≤ d) (k N : ℕ) (hkN : k ≤ N)
    (m : ℕ) (hmN : m ≤ d ^ (N + 1)) :
    (∑ j ∈ Finset.Icc k N, (d : ℚ) ^ j)
      ≥ (m : ℚ) * (d - 1 : ℚ)⁻¹ - (d : ℚ) ^ k / (d - 1) := by
  -- Rewrite Icc k N as Ico k (N+1) (Finset.Icc k N = Finset.Ico k (N+1) via Nat.Icc_eq_Ico? actually use `Finset.sum_Icc_eq_sum_range` or note Icc k N = Ico k (N+1)).
  have h_eq : ∑ j ∈ Finset.Icc k N, (d : ℚ) ^ j = (∑ j ∈ Finset.Ico k (N + 1), (d : ℚ) ^ j) := by
    rfl;
  rw [ h_eq, geom_sum_Ico ] <;> norm_num ; ring_nf;
  · exact mul_le_mul_of_nonneg_right ( by norm_cast; ring_nf at *; linarith ) ( inv_nonneg.mpr ( by linarith [ ( by norm_cast : ( 2 : ℚ ) ≤ d ) ] ) );
  · linarith;
  · linarith

/-- **Erdős 124 — structural bound (Lemma A).**
For a finite set `D` of bases all `≥ 2`, an exponent floor `k`, and a per-base top exponent
`J d ≥ k`, let `S(X) = ∑_{d∈D} ∑_{j=k}^{J d} d^j` be the sum of all merged atoms `d^j ≤ X`.
If `m` is at most the next atom `d^{J d+1}` for every base (in particular `m` is the smallest
next atom), then `S(X) ≥ m·β − C'` where `β = ∑_{d∈D} 1/(d−1)` and `C' = ∑_{d∈D} d^k/(d−1)`.

The proof is elementary: per base the geometric sum equals `(d^{J d+1} − d^k)/(d−1)`, which is
`≥ (m − d^k)/(d−1)` since `m ≤ d^{J d+1}`; summing over `D` gives the bound.

The hypotheses `hne` (nonemptiness of `D`) and `hk` (`k ≠ 0`), present in the requested
signature, are not needed for this bound and are kept only for fidelity to the statement. -/
theorem erdos124_gap_onset
    (D : Finset ℕ) (hD : ∀ d ∈ D, 2 ≤ d) (hne : D.Nonempty) (k : ℕ) (hk : k ≠ 0)
    (J : ℕ → ℕ) (hJk : ∀ d ∈ D, k ≤ J d)
    (m : ℕ) (hm : ∀ d ∈ D, m ≤ d ^ (J d + 1)) :
    (∑ d ∈ D, ∑ j ∈ Finset.Icc k (J d), (d : ℚ) ^ j)
      ≥ (m : ℚ) * (∑ d ∈ D, (d - 1 : ℚ)⁻¹) - ∑ d ∈ D, (d : ℚ) ^ k / (d - 1) := by
  rw [ Finset.mul_sum _ _ _ ];
  simpa only [ ← Finset.sum_sub_distrib ] using Finset.sum_le_sum fun x hx => by have := per_base_bound x ( hD x hx ) k ( J x ) ( hJk x hx ) m ( hm x hx ) ; ring_nf at this ⊢; linarith;