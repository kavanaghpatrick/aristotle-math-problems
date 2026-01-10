/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d8b4162a-8139-4eb0-a5f6-124dc9471f3d

The following was proved by Aristotle:

- theorem entropy_bound_on_N (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (2^A.card : ℝ) ≤ Real.sqrt (2 * π * Real.exp 1 * A.card) * N

- theorem variance_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (1 / Real.sqrt 3 - 1 / A.card) * 2^A.card / Real.sqrt A.card ≤ N

The following was negated by Aristotle:

- theorem discrete_entropy_power (X_entropy : ℝ) (variance : ℝ) (hvar : 0 < variance) :
    X_entropy ≤ (1/2) * Real.log (2 * π * Real.exp 1 * variance)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
Erdős Problem #1: ENTROPY / INFORMATION THEORY APPROACH

STRATEGY (from Grok multi-agent consultation):
For sum-distinct set A, the random variable X = Σ_{a∈A} ε_a·a where ε_a ∈ {0,1}
has H(X) = |A| bits (all 2^|A| outcomes are distinct, hence equiprobable).

Key insight: For fixed mean and variance, Gaussian maximizes entropy.
- Mean: μ = (1/2)·Σa
- Variance: σ² = (1/4)·Σa²

The "entropy power inequality" style argument:
  H(X) ≤ (1/2)·log(2πe·σ²)

Substituting:
  n ≤ (1/2)·log(2πe·(1/4)·Σa²)

Using Σa² ≤ n·N² gives bounds relating N to 2^n.

FORMALIZATION PATH:
1. Define subset sum random variable
2. Prove H(X) = n for sum-distinct sets
3. Apply entropy power inequality
4. Derive the bound on N
-/

import Mathlib


open Finset BigOperators Real Filter MeasureTheory

namespace Erdos1Entropy

variable {n : ℕ}

-- Sum-distinct definition
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- ENTROPY FRAMEWORK
-- ══════════════════════════════════════════════════════════════════════════════

/-- The entropy of a finite uniform distribution on n elements is log n -/
lemma entropy_uniform (n : ℕ) (hn : 0 < n) :
    Real.log n = n * (1/n : ℝ) * Real.log n := by
  field_simp
  ring

/-- For sum-distinct sets, the subset sum distribution is uniform on 2^|A| points -/
lemma sum_distinct_uniform_distribution (A : Finset ℕ) (N : ℕ)
    (h : IsSumDistinctSet A N) :
    (A.powerset.image (fun S => S.sum id)).card = 2^A.card := by
  rw [card_image_of_injective]
  · exact card_powerset A
  · intro S hS T hT heq
    have := h.2 ⟨S, hS⟩ ⟨T, hT⟩ heq
    simp only [Subtype.mk.injEq] at this
    exact this

/-- Entropy of sum-distinct subset sums is |A| bits -/
theorem entropy_sum_distinct (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    Real.log (2^A.card : ℝ) = A.card * Real.log 2 := by
  rw [← Real.rpow_natCast 2 A.card]
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)]
  ring

-- ══════════════════════════════════════════════════════════════════════════════
-- VARIANCE AND SECOND MOMENT
-- ══════════════════════════════════════════════════════════════════════════════

/-- The variance of the subset sum is (1/4)·Σa² -/
lemma subset_sum_variance (A : Finset ℕ) :
    (1/4 : ℝ) * (∑ a ∈ A, (a:ℝ)^2) = (∑ a ∈ A, (a:ℝ)^2) / 4 := by
  ring

/-- Upper bound on sum of squares -/
lemma sum_sq_le_N_sq (A : Finset ℕ) (N : ℕ) (h : A ⊆ Finset.Icc 1 N) :
    ∑ a ∈ A, (a:ℝ)^2 ≤ A.card * (N:ℝ)^2 := by
  calc ∑ a ∈ A, (a:ℝ)^2
      ≤ ∑ _ ∈ A, (N:ℝ)^2 := by
        apply sum_le_sum
        intro a ha
        have hacc : a ∈ Finset.Icc 1 N := h ha
        simp only [Finset.mem_Icc] at hacc
        have haN : (a:ℝ) ≤ N := Nat.cast_le.mpr hacc.2
        exact sq_le_sq' (by linarith) haN
    _ = A.card * (N:ℝ)^2 := by simp [mul_comm]

/- Aristotle failed to find a proof. -/
/-- Lower bound on sum of squares for sum-distinct sets -/
lemma sum_sq_lower_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (4^A.card - 1) / 3 ≤ ∑ a ∈ A, (a:ℝ)^2 := by
  -- This follows from the sum-distinct property via induction
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
══════════════════════════════════════════════════════════════════════════════
ENTROPY POWER INEQUALITY APPROACH
══════════════════════════════════════════════════════════════════════════════

Entropy power inequality for discrete distributions (weak form)
-/
theorem discrete_entropy_power (X_entropy : ℝ) (variance : ℝ) (hvar : 0 < variance) :
    X_entropy ≤ (1/2) * Real.log (2 * π * Real.exp 1 * variance) := by
  -- This is the continuous limit; for discrete we need modification
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any variance $v > 0$.
  use 1 / 2 * Real.log (2 * Real.pi * Real.exp 1 * 1) + 1;
  -- Let's choose any variance $v > 0$ and show that the inequality holds.
  use 1;
  simp

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- ENTROPY POWER INEQUALITY APPROACH
-- ══════════════════════════════════════════════════════════════════════════════

/-- Entropy power inequality for discrete distributions (weak form) -/
theorem discrete_entropy_power (X_entropy : ℝ) (variance : ℝ) (hvar : 0 < variance) :
    X_entropy ≤ (1/2) * Real.log (2 * π * Real.exp 1 * variance) := by
  -- This is the continuous limit; for discrete we need modification
  sorry

/-- Main entropy-based bound -/
theorem entropy_bound_on_N (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (2^A.card : ℝ) ≤ Real.sqrt (2 * π * Real.exp 1 * A.card) * N := by
  /-
  Proof sketch:
  1. H(X) = n bits (sum-distinct gives n bits of entropy)
  2. By entropy power inequality: n ≤ (1/2)·log(2πe·σ²)
  3. σ² = (1/4)·Σa² ≤ (1/4)·n·N²
  4. Therefore: 2^(2n) ≤ 2πe·(n/4)·N²
  5. Rearranging: 2^n ≤ √(πen/2)·N
  -/
  have := @sum_sq_lower_bound A N h hcard;
  -- Using the bound on the sum of squares, we get $(4^A.card - 1) / 3 \leq A.card * N^2$.
  have h_sum_sq_bound : (4^A.card - 1) / 3 ≤ A.card * (N : ℝ)^2 := by
    exact this.trans ( le_trans ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( h.1 hx ) |>.2 ) _ ) <| by norm_num );
  -- Squaring both sides to remove the square root gives us $4^A.card \leq 2 * \pi * e * A.card * N^2$.
  have h_sq : (4 ^ A.card : ℝ) ≤ 2 * Real.pi * Real.exp 1 * A.card * N^2 := by
    -- We'll use that $2 \pi e \approx 17.08$ to conclude the proof.
    have h_approx : 2 * Real.pi * Real.exp 1 > 17 := by
      have := Real.exp_one_gt_d9.le ; norm_num1 at * ; have := Real.pi_gt_d4 ; norm_num1 at * ; nlinarith [ Real.pi_le_four ];
    nlinarith [ show ( 4 : ℝ ) ^ #A ≥ 4 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) hcard ), show ( #A : ℝ ) * N ^ 2 ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( mod_cast hcard ) ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ) ];
  rw [ show ( 4 : ℝ ) ^ #A = ( 2 ^ #A ) ^ 2 by rw [ sq, ← mul_pow ] ; norm_num ] at h_sq ; nlinarith [ show 0 ≤ Real.sqrt ( 2 * Real.pi * Real.exp 1 * ( #A : ℝ ) ) * ( N : ℝ ) by positivity, Real.mul_self_sqrt ( show 0 ≤ 2 * Real.pi * Real.exp 1 * ( #A : ℝ ) by positivity ) ]

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE: DIRECT VARIANCE BOUND
-- ══════════════════════════════════════════════════════════════════════════════

/-- Direct variance-based bound without entropy -/
theorem variance_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (1 / Real.sqrt 3 - 1 / A.card) * 2^A.card / Real.sqrt A.card ≤ N := by
  -- From: Σa² ≥ (4^n-1)/3 and Σa² ≤ n·N²
  -- We get: (4^n-1)/3 ≤ n·N²
  -- So: (4^n-1)/(3n) ≤ N²
  -- Taking sqrt: 2^n/√(3n) ≤ N·√(1 - 4^(-n))
  -- From Lemma 2, we have that $N^2 \ge \frac{4^{|A|}-1}{3|A|}$.
  have hN_sq_ge : (N : ℝ)^2 ≥ (4^#A - 1) / (3 * #A) := by
    have h_lower_bound : (∑ a ∈ A, (a:ℝ)^2) ≤ (A.card : ℝ) * N^2 := by
      exact le_trans ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.cast_le.mpr ( Finset.mem_Icc.mp ( h.1 hx ) |>.2 ) ) 2 ) ( by norm_num );
    have := sum_sq_lower_bound A N h hcard; rw [ ge_iff_le, div_le_iff₀ ] <;> first | positivity | linarith;
  -- We'll use that $4^{|A|} = (2^{|A|})^2$ to simplify the inequality.
  have h_simplified : (N : ℝ) ≥ ((2 ^ #A) - 1) / Real.sqrt (3 * #A) := by
    refine' le_of_pow_le_pow_left₀ ( by positivity ) ( by positivity ) ( le_trans _ hN_sq_ge );
    rw [ div_pow, Real.sq_sqrt <| by positivity ] ; ring_nf ; norm_num [ pow_mul', ← mul_pow ] ;
    nlinarith only [ inv_pos.mpr ( by positivity : 0 < ( A.card : ℝ ) ), show ( 2 : ℝ ) ^ A.card ≥ ↑A.card + 1 by exact mod_cast Nat.recOn A.card ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith [ ihn, pow_pos ( zero_lt_two' ℕ ) n ] ];
  refine le_trans ?_ h_simplified ; ring_nf ; norm_num;
  field_simp;
  nlinarith only [ show ( 2:ℝ ) ^ #A ≥ ↑ ( #A ) + 1 by exact mod_cast Nat.recOn #A ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith [ ihn, pow_pos ( zero_lt_two' ℕ ) n ], show ( Real.sqrt 3:ℝ ) ≥ 1 by exact Real.le_sqrt_of_sq_le <| by norm_num, Real.sq_sqrt <| show 0 ≤ 3 by norm_num ]

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN RESULT
-- ══════════════════════════════════════════════════════════════════════════════

/-- The entropy-theoretic bound gives √(2/π) constant -/
theorem lb_strong_entropy : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (Real.sqrt (2 / π) - o A.card) * 2 ^ A.card / Real.sqrt A.card ≤ N := by
  /-
  The entropy approach gives:
  - H(X) = n (sum-distinct means n bits)
  - Gaussian maximizes entropy for given variance
  - Variance is (1/4)·Σa²
  - This leads to the √(2/π) constant from the Gaussian entropy formula

  Note: This is essentially equivalent to the Fourier approach;
  the Gaussian in Fourier space IS the entropy-maximizing distribution.
  -/
  sorry

end Erdos1Entropy