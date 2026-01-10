/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9373a94f-21fe-4213-8159-cee83a978521

The following was proved by Aristotle:

- theorem parseval_subset_sums (A : Finset ℕ) :
    ∑ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ)^2 =
    (1 / (2 * π)) * ∫ θ in Set.Icc (-π) π, ‖genPoly A (exp (I * θ))‖^2

- theorem parseval_sum_distinct (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    ∑ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ)^2 = 2^A.card
-/

/-
Erdős Problem #1: FOURIER ANALYSIS APPROACH

STRATEGY (from Gemini + Grok multi-agent consultation):
The generating function P(z) = ∏_{j=1}^n (1 + z^{a_j}) encodes subset sums.
For z = e^{iθ}, Parseval gives: (1/2π) ∫|P(e^{iθ})|² dθ = Σ_k (count of sums = k)²

Key insight: If sum-distinct, count ∈ {0,1}, so RHS = 2^n.
Near θ=0: cos(aθ) ≈ exp(-a²θ²/2), giving Gaussian behavior.
This leads to the √(2/π) constant via Gaussian integral.

FORMALIZATION PATH:
1. Define the generating polynomial P(z)
2. Prove Parseval identity for subset sum counts
3. Use Taylor expansion of cosine near 0
4. Derive the √(2/π) bound from Gaussian integral
-/

import Mathlib


open Finset BigOperators Complex Real Filter

namespace Erdos1Fourier

variable {n : ℕ}

-- Sum-distinct definition
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- GENERATING FUNCTION APPROACH
-- ══════════════════════════════════════════════════════════════════════════════

/-- The generating polynomial for subset sums -/
noncomputable def genPoly (A : Finset ℕ) (z : ℂ) : ℂ :=
  ∏ a ∈ A, (1 + z ^ a)

/-- Subset sum count function -/
def subsetSumCount (A : Finset ℕ) (k : ℕ) : ℕ :=
  (A.powerset.filter (fun S => S.sum id = k)).card

/-- For sum-distinct sets, count is always 0 or 1 -/
lemma sum_distinct_count_le_one (A : Finset ℕ) (N : ℕ)
    (h : IsSumDistinctSet A N) (k : ℕ) :
    subsetSumCount A k ≤ 1 := by
  unfold subsetSumCount
  by_contra hgt
  push_neg at hgt
  have hge2 : 2 ≤ (A.powerset.filter (fun S => S.sum id = k)).card := hgt
  obtain ⟨S, hS, T, hT, hne⟩ := Finset.one_lt_card.mp hge2
  simp only [mem_filter, mem_powerset] at hS hT
  have heq : S.sum id = T.sum id := by rw [hS.2, hT.2]
  have := h.2 ⟨S, mem_powerset.mpr hS.1⟩ ⟨T, mem_powerset.mpr hT.1⟩
  simp only [Subtype.mk.injEq] at this
  exact hne (this heq)

/-- Parseval's identity: ∫|P(e^{iθ})|² = 2π · Σ (count)² -/
theorem parseval_subset_sums (A : Finset ℕ) :
    ∑ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ)^2 =
    (1 / (2 * π)) * ∫ θ in Set.Icc (-π) π, ‖genPoly A (exp (I * θ))‖^2 := by
  -- By definition of $genPoly$, we know that $P(e^{iθ}) = \sum_{k=0}^{S} c_k e^{ikθ}$, where $c_k$ is the number of subsets of $A$ that sum to $k$.
  have h_genPoly : ∀ θ : ℝ, Erdos1Fourier.genPoly A (Complex.exp (Complex.I * θ)) = ∑ k ∈ Finset.range (A.sum id + 1), (Erdos1Fourier.subsetSumCount A k : ℂ) * Complex.exp (Complex.I * k * θ) := by
    -- By definition of $genPoly$, we know that $P(e^{iθ}) = \sum_{k=0}^{S} c_k e^{ikθ}$, where $c_k$ is the number of subsets of $A$ that sum to $k$. This follows from the generating function approach.
    have h_genPoly : ∀ θ : ℝ, Erdos1Fourier.genPoly A (Complex.exp (Complex.I * θ)) = ∑ S ∈ A.powerset, Complex.exp (Complex.I * (S.sum id) * θ) := by
      unfold Erdos1Fourier.genPoly;
      intro θ; simp +decide [ add_comm ( 1 : ℂ ), Finset.prod_add, ← Complex.exp_nat_mul ];
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, ← Complex.exp_sum ];
    intro θ
    rw [h_genPoly];
    have h_genPoly : ∀ θ : ℝ, ∑ S ∈ A.powerset, Complex.exp (Complex.I * (S.sum id) * θ) = ∑ k ∈ Finset.range (A.sum id + 1), (∑ S ∈ A.powerset, if S.sum id = k then Complex.exp (Complex.I * k * θ) else 0) := by
      intro θ; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
      rw [ Finset.filter_true_of_mem fun x hx => Nat.lt_succ_of_le <| Finset.sum_le_sum_of_subset <| Finset.mem_powerset.mp hx ];
    simp_all +decide [ Finset.sum_ite ];
    rfl;
  -- Using the definition of $P(e^{iθ})$, we can expand $|P(e^{iθ})|^2$ and then integrate term by term.
  have h_expand : ∀ θ : ℝ, ‖Erdos1Fourier.genPoly A (Complex.exp (Complex.I * θ))‖ ^ 2 = ∑ k ∈ Finset.range (A.sum id + 1), ∑ l ∈ Finset.range (A.sum id + 1), (Erdos1Fourier.subsetSumCount A k : ℝ) * (Erdos1Fourier.subsetSumCount A l : ℝ) * Real.cos ((k - l) * θ) := by
    intro θ; rw [ h_genPoly θ ] ; simp +decide [ Complex.normSq, Complex.sq_norm, Complex.exp_re, Complex.exp_im ] ; ring;
    simp +decide [ Real.cos_sub, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, pow_two ];
    simp +decide only [mul_add, sum_add_distrib];
  -- We can interchange the order of summation and integration.
  have h_interchange : ∫ θ in Set.Icc (-Real.pi) Real.pi, ‖Erdos1Fourier.genPoly A (Complex.exp (Complex.I * θ))‖ ^ 2 = ∑ k ∈ Finset.range (A.sum id + 1), ∑ l ∈ Finset.range (A.sum id + 1), (Erdos1Fourier.subsetSumCount A k : ℝ) * (Erdos1Fourier.subsetSumCount A l : ℝ) * ∫ θ in Set.Icc (-Real.pi) Real.pi, Real.cos ((k - l) * θ) := by
    simp +decide only [h_expand, ← MeasureTheory.integral_const_mul];
    rw [ MeasureTheory.integral_finset_sum ];
    · exact Finset.sum_congr rfl fun _ _ => by rw [ MeasureTheory.integral_finset_sum ] ; exact fun _ _ => by exact Continuous.integrableOn_Icc <| by exact Continuous.mul ( continuous_const.mul continuous_const ) <| Real.continuous_cos.comp <| by continuity;
    · exact fun _ _ => Continuous.integrableOn_Icc <| continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul continuous_const ) <| Real.continuous_cos.comp <| by continuity;
  -- We can evaluate the integral $\int_{-\pi}^{\pi} \cos((k-l)\theta) \, d\theta$.
  have h_integral : ∀ k l : ℕ, k ≠ l → ∫ θ in Set.Icc (-Real.pi) Real.pi, Real.cos ((k - l) * θ) = 0 := by
    intro k l hkl; rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ( by linarith [ Real.pi_pos ] ) ] ; rw [ intervalIntegral.integral_comp_mul_left ] ; norm_num;
    · exact Or.inr ( Real.sin_eq_zero_iff.mpr ⟨ k - l, by push_cast; ring ⟩ );
    · exact sub_ne_zero_of_ne <| Nat.cast_injective.ne hkl;
  rw [ h_interchange, Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i ( fun j hj => by by_cases hij : i = j <;> aesop ) ( by aesop ) ] ; norm_num [ Real.pi_pos.le ] ; ring_nf ; norm_num [ Real.pi_ne_zero ];
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ] ; ring

/-- For sum-distinct sets, Parseval RHS = 2^n -/
theorem parseval_sum_distinct (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    ∑ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ)^2 = 2^A.card := by
  have hle : ∀ k, subsetSumCount A k ≤ 1 := sum_distinct_count_le_one A N h
  -- Each count is 0 or 1, so count² = count
  -- Total count = 2^n (all subsets)
  -- Since the count is either 0 or 1, we have that the sum of the squares of the counts is equal to the sum of the counts.
  have hsum_eq : ∑ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ) ^ 2 = ∑ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ) := by
    exact Finset.sum_congr rfl fun x hx => by norm_cast; nlinarith only [ hle x, show Erdos1Fourier.subsetSumCount A x ≥ 0 from Nat.zero_le _ ] ;
  have hsum_count : ∑ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ) = ∑ S ∈ Finset.powerset A, 1 := by
    have hsum_count : ∀ k ∈ Finset.range (A.sum id + 1), (subsetSumCount A k : ℝ) = ∑ S ∈ Finset.powerset A, if S.sum id = k then 1 else 0 := by
      aesop
    rw [ Finset.sum_congr rfl hsum_count, Finset.sum_comm ];
    simp +zetaDelta at *;
    rw_mod_cast [ Finset.filter_true_of_mem fun x hx => Nat.lt_succ_of_le <| Finset.sum_le_sum_of_subset <| Finset.mem_powerset.mp hx ] ; simp +decide [ Finset.card_univ ];
  aesop

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Ambiguous term
  exp
Possible interpretations:
  rexp ((-θ ^ 2 * ∑ a ∈ A, (↑a : ℝ) ^ 2) / 2) : ℝ
  
  cexp (-(↑θ : ℂ) ^ 2 * (↑(∑ a ∈ A, (↑a : ℝ) ^ 2) : ℂ) / 2) : ℂ-/
-- ══════════════════════════════════════════════════════════════════════════════
-- GAUSSIAN APPROXIMATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Near θ=0, |P(e^{iθ})|² ≈ 2^{2n} · exp(-θ² · Σa²/2) -/
theorem gen_poly_gaussian_approx (A : Finset ℕ) (θ : ℝ) (hsmall : |θ| ≤ 1) :
    ∃ C > 0, |‖genPoly A (exp (I * θ))‖^2 - 2^(2*A.card) * exp (-θ^2 * (∑ a ∈ A, (a:ℝ)^2) / 2)|
    ≤ C * θ^4 * 2^(2*A.card) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Ambiguous term
  exp
Possible interpretations:
  rexp (-θ ^ 2 * σ ^ 2 / 2) : ℝ
  
  cexp (-(↑θ : ℂ) ^ 2 * σ ^ 2 / 2) : ℂ
failed to synthesize
  HDiv ℂ ℂ ℝ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- The Gaussian integral gives the √(2/π) factor -/
theorem gaussian_integral_factor :
    ∫ θ in Set.Icc (-π) π, exp (-θ^2 * σ^2 / 2) = sqrt (2 * π / σ^2) := by
  sorry

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN RESULT: √(2/π) BOUND
-- ══════════════════════════════════════════════════════════════════════════════

/-- The Elkies-Gleason bound via Fourier analysis -/
theorem lb_strong_fourier : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (√(2 / π) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  /-
  Proof sketch:
  1. By Parseval, ∫|P|² = 2π · 2^n for sum-distinct sets
  2. Near θ=0, |P|² ≈ 2^{2n} · exp(-θ²·Σa²/2)
  3. The Gaussian integral contributes √(2π/Σa²) to the normalization
  4. Using Σa² ≥ (4^n-1)/3 and the peak dominates, get the bound
  -/
  sorry

end Erdos1Fourier