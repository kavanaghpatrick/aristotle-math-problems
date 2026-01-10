/-
Erdős Problem #1: Prove lb_strong INDEPENDENTLY (without using erdos_1)

CONTEXT:
- lb_variance is PROVEN: N ≥ (1/√3 - o(1)) · 2ⁿ/√n
- lb_strong uses erdos_1 (which has sorry) via exact?
- GOAL: Prove lb_strong directly without erdos_1

TARGET CONSTANT IMPROVEMENT:
- Current: 1/√3 ≈ 0.577
- Target: √(2/π) ≈ 0.798
- Factor: 1.38× improvement needed

ELKIES-GLEASON APPROACH:
The key insight is that subset sums of a sum-distinct set behave like
a random walk. For random ±a_i contributions, by CLT:
  - Subset sums are approximately Gaussian
  - Variance = (1/4)∑a²
  - For 2ⁿ distinct points in [0, nN], need "spacing" ≈ nN/2ⁿ
  - By Gaussian tail bounds: this forces N ≥ √(2/π) · 2ⁿ/√n

PROOF STRATEGY:
1. Use variance_identity: ∑_S (sum(S) - μ)² = 2^n/4 · ∑a²
2. The 2ⁿ distinct subset sums have total "spread" proportional to √(∑a²·2ⁿ)
3. They must fit in [0, nN], so nN ≥ c · √(∑a²·2ⁿ) for some c
4. Combined with ∑a² ≥ (4ⁿ-1)/3, get the improved bound
-/

import Mathlib

open Filter Finset

open scoped Topology Real BigOperators

namespace Erdos1

-- Definition from proven file
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from Aristotle 244de51c)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section

/-- Variance identity for subset sums -/
lemma variance_identity (A : Finset ℕ) :
  ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ)) - (∑ x ∈ A, (x : ℝ)) / 2)^2 =
  (2 : ℝ)^(A.card) / 4 * ∑ a ∈ A, (a : ℝ)^2 := by
  induction' A using Finset.induction with a A ha ih
  · norm_num
  · have h_split : ∑ s ∈ (Insert.insert a A).powerset,
        (∑ x ∈ s, (x : ℝ) - (∑ x ∈ Insert.insert a A, (x : ℝ)) / 2) ^ 2 =
        ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ) - (∑ x ∈ A, (x : ℝ)) / 2) + (a : ℝ) / 2) ^ 2 +
        ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ) - (∑ x ∈ A, (x : ℝ)) / 2) - (a : ℝ) / 2) ^ 2 := by
      simp +decide [Finset.sum_powerset_insert ha]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine' Finset.sum_congr rfl fun x hx => _
      rw [Finset.sum_insert (Finset.notMem_mono (Finset.mem_powerset.mp hx) ha)]
      ring
      grind
    simp_all +decide [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_sq, add_sq]
    ring
    norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _]
    ring

/-- Variance lower bound for integer-spaced reals -/
lemma variance_lower_bound (A : Finset ℝ) (h_dist : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|) :
  ∑ x ∈ A, x^2 - (∑ x ∈ A, x)^2 / A.card ≥ ((A.card : ℝ)^3 - A.card) / 12 := by
  sorry  -- PROVEN in 244de51c, copy full proof if needed

/-- Sum of squares lower bound for sum-distinct sets -/
lemma sum_sq_lower_bound (A : Finset ℕ) (h_inj : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
  ∑ a ∈ A, (a : ℝ)^2 ≥ ((2 : ℝ)^(2 * A.card) - 1) / 3 := by
  sorry  -- PROVEN in 244de51c, copy full proof if needed

/-- The lb bound (Erdős-Moser 1956) -/
theorem lb : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  sorry  -- PROVEN in 244de51c

/-- The lb_variance bound (1/√3 constant) - FULLY PROVEN -/
theorem lb_variance : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / Real.sqrt 3 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  sorry  -- PROVEN in 244de51c

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: PROVE lb_strong INDEPENDENTLY
-- ══════════════════════════════════════════════════════════════════════════════

/-
Key lemma: The "spread" of 2ⁿ subset sums requires a container of size
proportional to √(variance · 2ⁿ).

For 2ⁿ distinct integers in [0, M], the variance is at least (2ⁿ)²/12 roughly.
The subset sums have variance = 2^n/4 · ∑a² by variance_identity.
The container [0, nN] has size nN.

The insight: 2ⁿ "evenly spaced" points in [0, nN] have spacing nN/2ⁿ.
But subset sums cluster more than uniform (they're roughly Gaussian).
The Gaussian approximation gives the √(2/π) factor.
-/

/-- Subset sums form a set of 2ⁿ distinct naturals -/
lemma subset_sums_card (A : Finset ℕ) (h : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
  rw [card_image_of_injOn]
  · exact card_powerset A
  · intro x hx y hy hxy
    have := @h ⟨x, hx⟩ ⟨y, hy⟩
    simp at this
    exact this hxy

/-- All subset sums are at most n·N -/
lemma subset_sum_le (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Icc 1 N) (S : Finset ℕ) (hS : S ⊆ A) :
    S.sum id ≤ A.card * N := by
  calc S.sum id
      ≤ A.sum id := sum_le_sum_of_subset hS
    _ ≤ A.card * N := by
        apply Finset.sum_le_card_nsmul
        intro x hx
        exact (mem_Icc.mp (hA hx)).2

/-- The mean of subset sums -/
def mean_sum (A : Finset ℕ) : ℝ := (∑ x ∈ A, (x : ℝ)) / 2

/-- Subset sums have bounded L² distance from mean -/
lemma subset_sums_L2_from_mean (A : Finset ℕ) :
    ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ)) - mean_sum A)^2 =
    (2 : ℝ)^(A.card) / 4 * ∑ a ∈ A, (a : ℝ)^2 := by
  unfold mean_sum
  exact variance_identity A

/--
MAIN GOAL: Prove lb_strong WITHOUT using erdos_1.

The approach: Use the Chebyshev/concentration inequality.
If 2ⁿ points have variance V, then they span at least √(V·2ⁿ/π) in some sense.
-/
theorem lb_strong_independent : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (√(2 / π) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  /-
  Strategy:
  1. From variance_identity: total squared deviation = 2^n/4 · ∑a²
  2. From sum_sq_lower_bound: ∑a² ≥ (4^n - 1)/3
  3. So total squared deviation ≥ 2^n/4 · (4^n - 1)/3 ≈ 2^(3n)/12

  4. For 2ⁿ distinct reals x₁,...,x_{2ⁿ} in [0, nN] with mean μ:
     ∑(xᵢ - μ)² = 2ⁿ · Var(x)

  5. For discrete uniform on [0, M]: Var = M²/12
     But subset sums are more concentrated (Gaussian-like)

  6. The key is: 2ⁿ points in [0, nN] with total squared deviation D
     must satisfy nN ≥ c · √(D/2ⁿ) for some c related to √(2/π)
  -/
  sorry

-- Alternative approach: use moments
/-- Second moment of subset sums -/
def second_moment (A : Finset ℕ) : ℝ :=
  (1 / 2^A.card : ℝ) * ∑ s ∈ A.powerset, (∑ x ∈ s, (x : ℝ))^2

/-- The second moment relates to sum of squares -/
lemma second_moment_formula (A : Finset ℕ) :
    second_moment A = (∑ a ∈ A, (a : ℝ))^2 / 4 + (∑ a ∈ A, (a : ℝ)^2) / 4 := by
  sorry

/--
Alternative: Show the optimal packing of 2ⁿ integers with given variance
in an interval of size M requires M ≥ √(2πn) · σ asymptotically.
-/
theorem packing_lower_bound (n : ℕ) (points : Fin (2^n) → ℕ)
    (h_distinct : Function.Injective points)
    (M : ℕ) (h_bound : ∀ i, points i ≤ M)
    (σ_sq : ℝ) (h_var : ∑ i, ((points i : ℝ) - (∑ j, (points j : ℝ)) / 2^n)^2 / 2^n ≥ σ_sq) :
    (M : ℝ) ≥ Real.sqrt (2 / π) * Real.sqrt (σ_sq * 2^n) / Real.sqrt n := by
  sorry

end

end Erdos1
