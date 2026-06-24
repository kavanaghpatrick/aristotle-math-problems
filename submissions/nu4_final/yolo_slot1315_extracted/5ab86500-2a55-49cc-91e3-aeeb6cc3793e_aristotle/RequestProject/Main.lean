import Mathlib
import RequestProject.Definitions
import RequestProject.ABCHelpers
import RequestProject.LowerBound

/-!
# Erdős Problem 938 — abc-conditional sandwich theorem

Conditional on the abc conjecture, the common difference `d` of any
consecutive powerful 3-AP `(n_k, n_{k+1}, n_{k+2})` satisfies:

  c_ε · N^{1/2 - ε} < d < 2·√N + 2

where `N = n_k`, for all sufficiently large `N`.

## Structure of the proof

* **Upper bound** (`upper_bound_common_diff`): Fully proved.  Uses the
  consecutive-square interloper argument: any interval of length > 2√N + 1
  starting at N contains a perfect square, which is powerful and forces
  `d ≤ 2√N + 1 < 2√N + 2`.

* **Lower bound** (`lower_bound_common_diff` in `LowerBound.lean`): States that
  under abc, `d > c_ε · N^{1/2-ε}`.  This relies on Chan 2022
  (arXiv:2210.00281, Theorem 2) applied via abc to the identity
  `n₁² = n₀ · n₂ + d²`.  The proof of this bound is marked sorry and requires
  a refined analysis of the coprime structure and gcd interactions.

* **Combination** (`erdos_938_abc_sandwich`): Combines both bounds.
-/

open scoped BigOperators Real
open Classical

set_option maxHeartbeats 8000000

noncomputable instance : DecidablePred Nat.Powerful := inferInstance

/-! ## Helper lemmas for the upper bound -/

/-- No powerful number exists strictly between consecutive powerful numbers
    in the enumeration. -/
lemma no_powerful_between_consecutive (k : ℕ) (m : ℕ) (hm : Nat.Powerful m)
    (h1 : Nat.nth Nat.Powerful k < m) (h2 : m < Nat.nth Nat.Powerful (k + 1)) : False := by
  contrapose! h2
  rw [Nat.nth_eq_sInf]
  refine' Nat.sInf_le ⟨hm, ?_⟩
  intro i hi
  exact lt_of_le_of_lt
    (Nat.nth_monotone (show {n | Nat.Powerful n}.Infinite from powerful_infinite)
      (Nat.le_of_lt_succ hi)) h1

/-- If an interval `(a, a + L)` has length `L > 2 * Nat.sqrt a + 1`,
    it contains a perfect square. -/
lemma interval_contains_square (a L : ℕ) (hL : L > 2 * Nat.sqrt a + 1) (_ha : 0 < a) :
    ∃ m : ℕ, 0 < m ∧ a < m ^ 2 ∧ m ^ 2 < a + L := by
  exact ⟨Nat.sqrt a + 1, Nat.succ_pos _,
    by linarith [Nat.lt_succ_sqrt a],
    by linarith [Nat.sqrt_le a]⟩

/-- Perfect squares (of positive numbers) are powerful. -/
lemma sq_powerful (m : ℕ) (hm : 0 < m) : Nat.Powerful (m ^ 2) := powerful_sq m hm

/-- Consecutive powerful numbers are strictly increasing. -/
lemma powerful_nth_strictMono : StrictMono (Nat.nth Nat.Powerful) :=
  Nat.nth_strictMono powerful_infinite

/-! ## Upper bound -/

/-- **Upper bound**: `d < 2√N + 2` for the common difference of a consecutive
    powerful 3-AP.  This is the consecutive-square interloper argument. -/
lemma upper_bound_common_diff (k : ℕ) :
    let n0 := Nat.nth Nat.Powerful k
    let n1 := Nat.nth Nat.Powerful (k + 1)
    let n2 := Nat.nth Nat.Powerful (k + 2)
    n1 - n0 = n2 - n1 →
    ((n1 - n0 : ℝ) < 2 * Real.sqrt n0 + 2) := by
  intro n0 n1 n2 h_eq
  have h_upper : (n1 : ℝ) - n0 ≤ 2 * Real.sqrt n0 + 1 := by
    have h_contradiction : ∀ m : ℕ, 0 < m → n0 < m^2 → m^2 < n2 → m^2 = n1 := by
      intros m hm_pos hm_gt_n0 hm_lt_n2
      have h_m_powerful : Nat.Powerful (m^2) := sq_powerful m hm_pos
      apply le_antisymm
      · grind +suggestions
      · apply Nat.le_of_not_lt; intro h_lt_n1
        exact no_powerful_between_consecutive k (m ^ 2) h_m_powerful hm_gt_n0 h_lt_n1
    set m := Nat.sqrt n0 + 1
    have hm_sq : n0 < m^2 := Nat.lt_succ_sqrt' n0
    by_cases hm_sq_lt_n2 : m^2 < n2
    · rw [← h_contradiction m (Nat.succ_pos _) hm_sq hm_sq_lt_n2]
      simp +zetaDelta at *
      nlinarith only [Real.sqrt_nonneg n0, Real.sq_sqrt <| Nat.cast_nonneg n0,
        show (Nat.sqrt n0 : ℝ) ^ 2 ≤ n0 from mod_cast Nat.sqrt_le' n0,
        show (Nat.sqrt n0 : ℝ) ≥ 0 by positivity]
    · have h1 : n2 ≤ m^2 := by linarith
      have h2 : n1 ≤ m^2 :=
        le_trans (Nat.nth_monotone
          (show {n : ℕ | Nat.Powerful n}.Infinite from powerful_infinite)
          (Nat.le_succ _)) h1
      have h3 : (n1 : ℝ) ≤ (Nat.sqrt n0 + 1)^2 := by exact_mod_cast h2
      nlinarith only [Real.sqrt_nonneg n0, Real.sq_sqrt <| Nat.cast_nonneg n0,
        show (n0.sqrt : ℝ) ≤ Real.sqrt n0 from
          Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' n0, h3]
  linarith

/-! ## Main theorem -/

/-- **Erdős Problem 938 — abc-conditional sandwich theorem.**

Under the abc conjecture, for every `ε > 0` there exists `K_ε` such that
for any index `k` with `n_k ≥ K_ε`, if `(n_k, n_{k+1}, n_{k+2})` form a
3-term arithmetic progression of consecutive powerful numbers, then

    n_k^{1/2 - ε} < n_{k+1} - n_k < 2√n_k + 2.

The upper bound is unconditional (consecutive-square interloper constraint).
The lower bound requires abc (Chan 2022, arXiv:2210.00281, Theorem 2). -/
theorem erdos_938_abc_sandwich (h_abc : ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
      (ABC.radical (a * b * c) : ℝ)^(1 + ε) < c}.Finite) :
    ∀ ε : ℝ, 0 < ε → ∃ K_ε : ℕ, ∀ k : ℕ,
      let n0 := Nat.nth Nat.Powerful k
      let n1 := Nat.nth Nat.Powerful (k+1)
      let n2 := Nat.nth Nat.Powerful (k+2)
      n0 ≥ K_ε → n1 - n0 = n2 - n1 →
      (((n1 - n0 : ℝ) > (n0 : ℝ)^(1/2 - ε)) ∧
       ((n1 - n0 : ℝ) < 2 * Real.sqrt n0 + 2)) := by
  intro ε hε
  obtain ⟨K_ε, hK_ε⟩ := lower_bound_common_diff h_abc ε hε
  refine ⟨K_ε, fun k hk₁ hk₂ => ⟨hK_ε k hk₁ hk₂, ?_⟩⟩
  convert upper_bound_common_diff k hk₂ using 1
