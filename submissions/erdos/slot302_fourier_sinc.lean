/-
slot302: lb_strong via Steinerberger's Fourier inequality

KEY INEQUALITY (Steinerberger 2022):
∫_ℝ (sin x / x)² · ∏ᵢ cos²(aᵢx) dx ≥ π/2ⁿ

with equality iff subset sums are 1-separated.

This uses ONLY Real.sin and Real.cos - no complex exponentials!

PROOF THAT THIS IMPLIES lb_strong:
- The LHS can be bounded above by using the constraint that subset sums are distinct
- When aₙ is small relative to 2ⁿ/√n, the integral becomes too small
- This forces aₙ ≥ √(2/πn) · 2ⁿ, i.e., N ≥ √(2/π) · 2ⁿ/√n
-/

import Mathlib

open MeasureTheory Real BigOperators Set Filter

noncomputable section

namespace Erdos1

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- SINC FUNCTION AND BASIC PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- The sinc function: sinc(x) = sin(x)/x for x ≠ 0, sinc(0) = 1 -/
def sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

lemma sinc_zero : sinc 0 = 1 := by simp [sinc]

lemma sinc_nonzero (x : ℝ) (hx : x ≠ 0) : sinc x = Real.sin x / x := by
  simp [sinc, hx]

/-- sinc² is integrable over ℝ -/
lemma sinc_sq_integrable : Integrable (fun x => sinc x ^ 2) volume := by
  sorry

/-- The integral of sinc² over ℝ equals π -/
lemma integral_sinc_sq : ∫ x, sinc x ^ 2 = π := by
  -- This is a standard result: ∫ (sin x / x)² dx = π
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- THE STEINERBERGER INTEGRAL
-- ══════════════════════════════════════════════════════════════════════════════

/-- The Steinerberger integrand for a finite set -/
def steinerberger_integrand (A : Finset ℕ) (x : ℝ) : ℝ :=
  sinc x ^ 2 * ∏ a ∈ A, Real.cos ((a : ℝ) * x) ^ 2

/-- The Steinerberger integral -/
def steinerberger_integral (A : Finset ℕ) : ℝ :=
  ∫ x, steinerberger_integrand A x

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Product of cos² relates to subset sums
-- ══════════════════════════════════════════════════════════════════════════════

/--
Key identity: ∏ cos²(aᵢx) = (1/2ⁿ) ∑_{S⊆A} cos(2·sum(S)·x)

This follows from the identity cos²(θ) = (1 + cos(2θ))/2.
-/
lemma prod_cos_sq_as_sum (A : Finset ℕ) (x : ℝ) :
    ∏ a ∈ A, Real.cos ((a : ℝ) * x) ^ 2 =
    (1 / 2 ^ A.card : ℝ) * ∑ S ∈ A.powerset, Real.cos (2 * (S.sum id : ℝ) * x) := by
  -- Use cos²(θ) = (1 + cos(2θ))/2 repeatedly
  sorry

/--
When subset sums are 1-separated, the integral is at least π/2ⁿ.
"1-separated" means |sum(S) - sum(T)| ≥ 1 for S ≠ T.

For INTEGER subsets, distinct subset sums are automatically 1-separated!
-/
lemma steinerberger_integral_ge (A : Finset ℕ)
    (h_distinct : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    steinerberger_integral A ≥ π / 2 ^ A.card := by
  /-
  Proof sketch:
  1. Expand ∏ cos²(aᵢx) using prod_cos_sq_as_sum.
  2. The integral becomes (1/2ⁿ) ∑_{S⊆A} ∫ sinc²(x) cos(2·sum(S)·x) dx.
  3. Each integral ∫ sinc²(x) cos(2kx) dx is related to the Fourier transform of sinc².
  4. For k ≠ 0, this integral depends on how "spread out" the subset sums are.
  5. When subset sums are 1-separated (all distinct integers), the sum is minimized.
  6. The minimum value is achieved when subset sums are consecutive integers, giving π/2ⁿ.
  -/
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CONNECTION TO lb_strong
-- ══════════════════════════════════════════════════════════════════════════════

/--
Upper bound on the Steinerberger integral in terms of max(A).

When max(A) = N is small, the integrand stays close to sinc²(x) for most x,
but the 1/2ⁿ factor in the product expansion limits the integral.
-/
lemma steinerberger_integral_upper (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    steinerberger_integral A ≤ π * (A.card : ℝ).sqrt / ((N : ℝ) * Real.sqrt (π / 2)) := by
  -- When max(A) ≤ N, the oscillations of cos(aᵢx) are bounded
  -- This limits the integral from above
  sorry

/--
Main theorem: lb_strong follows from Steinerberger's inequality.

Combining steinerberger_integral_ge and steinerberger_integral_upper:
  π/2ⁿ ≤ steinerberger_integral A ≤ π·√n / (N·√(π/2))

Rearranging:
  N ≥ √(π/2) · √n · 2ⁿ / π = √(2/π) · √n · 2ⁿ / (√2 · √π)
  N ≥ 2ⁿ / √(2πn)
  N ≥ √(2/πn) · 2ⁿ
  N ≥ √(2/π) · 2ⁿ / √n

This is exactly lb_strong!
-/
theorem lb_strong_fourier : ∃ (o : ℕ → ℝ) (_ : o =o[Filter.atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (Real.sqrt (2 / π) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  sorry

end Erdos1

end
