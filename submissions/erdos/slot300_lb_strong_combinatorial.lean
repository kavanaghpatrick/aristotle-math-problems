/-
slot300: lb_strong via combinatorial approach (Dubroff-Fox-Xu style)

KEY INSIGHT: Prove max(A) ≥ C(n, ⌊n/2⌋) for sum-distinct A.
Since C(n, n/2) ≈ 2^n / √(πn/2), this gives the √(2/π) bound.

The argument:
- Consider the 2^n subsets of A, each with a distinct sum
- The subset sums partition into pairs: S and S ∪ {max(A)}
- These pairs are "shifted" by max(A)
- By injectivity + counting, max(A) must be large enough
-/

import Mathlib

open Finset BigOperators

noncomputable section

namespace Erdos1

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- CENTRAL BINOMIAL COEFFICIENT APPROACH
-- ══════════════════════════════════════════════════════════════════════════════

/-- The central binomial coefficient C(n, ⌊n/2⌋) -/
def centralBinom (n : ℕ) : ℕ := n.choose (n / 2)

/-- Asymptotic: C(n, n/2) ~ 2^n / √(πn/2) -/
lemma centralBinom_asymptotic (n : ℕ) (hn : n ≥ 1) :
    (centralBinom n : ℝ) ≥ 2^n / Real.sqrt (Real.pi * n / 2 + 1) := by
  -- Stirling approximation gives C(n, n/2) ~ 2^n · √(2/(πn))
  -- We use a slightly weaker bound that's easier to prove
  sorry

/-- KEY LEMMA: For sum-distinct A, max(A) ≥ |A.powerset.filter (·.card = |A|/2)| -/
lemma max_ge_half_subsets (A : Finset ℕ) (hA : A.Nonempty)
    (h_inj : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    A.max' hA ≥ (A.powerset.filter (fun S => S.card = A.card / 2)).card := by
  /-
  Proof idea (Dubroff-Fox-Xu):
  Let a = max(A), and consider subsets of A \ {a}.
  For each subset S ⊆ A \ {a}, the sums S.sum and (S ∪ {a}).sum differ by a.

  The 2^(n-1) subsets of A \ {a} map to 2^(n-1) distinct sums in [0, sum(A) - a].
  The 2^(n-1) subsets containing a map to 2^(n-1) distinct sums in [a, sum(A)].

  By sum-distinctness, these 2^n sums are all different.
  The "gap" between the two ranges forces a to be at least C(n-1, (n-1)/2).

  More precisely: among subsets NOT containing a, how many can have sum < a?
  At most C(n-1, (n-1)/2) by a counting argument.
  So a ≥ C(n-1, (n-1)/2) + 1 ≈ C(n, n/2) / 2.

  But we want the stronger bound...
  -/
  sorry

/-- The subset sums "fill" an interval, so the interval must be large enough -/
lemma interval_size_from_distinctness (A : Finset ℕ) (N : ℕ)
    (hA : IsSumDistinctSet A N) :
    N * A.card ≥ 2^A.card - 1 := by
  -- Subset sums are in [0, ∑a] ⊆ [0, N·|A|]
  -- There are 2^|A| distinct sums, so N·|A| ≥ 2^|A| - 1
  have h_sums_in_range : ∀ S ∈ A.powerset, S.sum id ≤ A.card * N := by
    intro S hS
    calc S.sum id ≤ A.sum id := sum_le_sum_of_subset (mem_powerset.mp hS)
      _ ≤ A.card * N := by
          apply Finset.sum_le_card_nsmul
          intro x hx
          exact (mem_Icc.mp (hA.1 hx)).2
  -- The number of distinct sums is 2^|A|
  have h_card : (A.powerset.image (fun S => S.sum id)).card = 2^A.card := by
    rw [card_image_of_injOn]
    · exact card_powerset A
    · intro x hx y hy hxy
      have := @hA.2 ⟨x, hx⟩ ⟨y, hy⟩
      simp at this
      exact this hxy
  -- So we need at least 2^|A| distinct values in [0, N·|A|]
  by_contra h_contra
  push_neg at h_contra
  -- If N·|A| < 2^|A| - 1, can't fit 2^|A| distinct values
  have h_range : (A.powerset.image (fun S => S.sum id)) ⊆ Icc 0 (A.card * N) := by
    intro s hs
    simp only [mem_image, mem_powerset] at hs
    obtain ⟨S, hS, rfl⟩ := hs
    simp only [mem_Icc, Nat.zero_le, true_and]
    exact h_sums_in_range S (mem_powerset.mpr hS)
  have := card_le_card h_range
  simp only [card_Icc, Nat.add_sub_cancel] at this
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: lb_strong via combinatorial bound
-- ══════════════════════════════════════════════════════════════════════════════

/-- lb_strong: The √(2/π) bound on sum-distinct sets -/
theorem lb_strong_combinatorial : ∃ (o : ℕ → ℝ) (_ : o =o[Filter.atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  /-
  Strategy: Show N ≥ C(|A|, |A|/2) / something small.

  From centralBinom_asymptotic: C(n, n/2) ≥ 2^n / √(πn/2 + 1)

  If we can show N ≥ C(n, n/2) / n (or similar), then:
  N ≥ 2^n / (n · √(πn/2 + 1))
    = 2^n / √(πn³/2 + n²)
    ≈ 2^n / √(πn³/2)
    = √(2/π) · 2^n / √n³
    = √(2/π) · 2^n / (n · √n)

  Hmm, this gives an extra factor of √n...

  Let me reconsider. The correct statement is:
  N ≥ (√(2/π) - o(1)) · 2^n / √n

  From the combinatorial bound: max(A) ≥ something involving C(n, n/2).

  The Dubroff-Fox-Xu paper shows: max(A) ≥ C(n, ⌊n/2⌋).

  C(n, n/2) ≈ 2^n · √(2/(πn))

  So max(A) ≥ √(2/(πn)) · 2^n = √(2/π) · 2^n / √n.

  This is EXACTLY the lb_strong bound!
  -/
  sorry

end Erdos1

end
