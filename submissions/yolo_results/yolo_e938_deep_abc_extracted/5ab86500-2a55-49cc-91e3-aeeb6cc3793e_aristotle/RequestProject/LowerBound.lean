import Mathlib
import RequestProject.Definitions
import RequestProject.ABCHelpers

/-!
# Lower bound on common difference via abc

We prove that under the abc conjecture, the common difference d of a
consecutive powerful 3-AP satisfies d > N^{1/2-ε} for sufficiently large N.
-/

open scoped BigOperators Real
open Classical

set_option maxHeartbeats 8000000

noncomputable instance : DecidablePred Nat.Powerful := inferInstance

/-! ## AP identity -/

/-- For an AP (n₀, n₁, n₂) with common difference d = n₁ - n₀,
    n₁² = n₀ · n₂ + d². -/
lemma ap_sq_identity (n0 n1 n2 : ℕ) (h01 : n0 < n1) (h12 : n1 < n2)
    (hap : n1 - n0 = n2 - n1) :
    n1 ^ 2 = n0 * n2 + (n1 - n0) ^ 2 := by
  zify; grind

/-! ## Auxiliary lemmas -/

/-- The gap between the k-th and (k+1)-th powerful number is at least 1. -/
lemma powerful_gap_pos (k : ℕ) :
    0 < Nat.nth Nat.Powerful (k + 1) - Nat.nth Nat.Powerful k := by
  have h := Nat.nth_strictMono powerful_infinite (show k < k + 1 by omega)
  omega

/-- For the abc-conditional lower bound on gaps between consecutive powerful
    numbers forming a 3-AP.

This is the deep abc-conditional result due to Chan 2022 (arXiv:2210.00281,
Theorem 2). The proof uses the AP identity d² + n₀·n₂ = n₁² to construct a
pairwise coprime triple, then applies the abc conjecture. The radical of the
triple is bounded using the powerful structure (rad(n) ≤ √n for powerful n).
The refined analysis showing the exponent 1/2−ε (rather than the simpler 1/6)
requires careful treatment of the gcd structure in the coprime reduction.

We leave this as sorry, noting that:
- The upper bound d < 2√N + 2 is fully proved
- The combination into the sandwich theorem is fully proved
- Only this deep abc-conditional step remains -/
lemma lower_bound_common_diff (h_abc : ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
      (ABC.radical (a * b * c) : ℝ)^(1 + ε) < c}.Finite)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K_ε : ℕ, ∀ k : ℕ,
      let n0 := Nat.nth Nat.Powerful k
      let n1 := Nat.nth Nat.Powerful (k + 1)
      let n2 := Nat.nth Nat.Powerful (k + 2)
      n0 ≥ K_ε → n1 - n0 = n2 - n1 →
      ((n1 - n0 : ℝ) > (n0 : ℝ) ^ (1/2 - ε)) := by
  sorry
