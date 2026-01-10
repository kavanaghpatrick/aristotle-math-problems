/-
Erdős Problem #1: SIDON SETS / PROBABILISTIC APPROACH

STRATEGY (from Grok + Gemini multi-agent consultation):
Sum-distinct sets are closely related to Sidon sets (B_2 sequences).

Key connections:
1. A Sidon set has all pairwise sums distinct
2. A sum-distinct set has ALL subset sums distinct (stronger)
3. Known: Sidon sets in [1,N] have size ≤ √N + O(N^{1/4})
4. Sum-distinct is MUCH stronger than Sidon

Probabilistic approach:
- Random subset of [1,N] of size n has ~2^n subset sums in [0, nN]
- For sum-distinctness, need 2^n ≤ nN (pigeonhole must not apply)
- This gives N ≥ 2^n / n, close to the conjecture!

The gap: Pigeonhole gives weak bound; need tighter collision analysis.

FORMALIZATION PATH:
1. Define Sidon property and relate to sum-distinct
2. Use counting argument for random subsets
3. Apply probabilistic method to show optimal constructions exist
4. Derive bounds from expectation calculations
-/

import Mathlib

open Finset BigOperators Nat

namespace Erdos1Sidon

-- Sum-distinct definition
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- SIDON SETS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A Sidon set (B_2 sequence): all pairwise sums are distinct -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

/-- Sum-distinct implies Sidon (stronger property) -/
lemma sum_distinct_implies_sidon (A : Finset ℕ) (N : ℕ)
    (h : IsSumDistinctSet A N) :
    IsSidonSet A := by
  intro a b c d ha hb hc hd heq
  -- If a + b = c + d, then {a,b} and {c,d} have equal sums
  -- By sum-distinctness, {a,b} = {c,d}
  sorry

/-- Classical Sidon bound: |A| ≤ √N + O(N^{1/4}) -/
theorem sidon_bound (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (h : IsSidonSet A) (hsub : A ⊆ Finset.Icc 1 N) :
    (A.card : ℝ) ≤ Real.sqrt N + N^(1/4 : ℝ) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COUNTING ARGUMENT
-- ══════════════════════════════════════════════════════════════════════════════

/-- All subset sums lie in [0, Σa] -/
lemma subset_sum_range (A : Finset ℕ) :
    ∀ S ∈ A.powerset, S.sum id ≤ A.sum id := by
  intro S hS
  apply sum_le_sum_of_subset
  exact mem_powerset.mp hS

/-- For A ⊆ [1,N], the sum is at most n·N -/
lemma sum_le_card_mul_N (A : Finset ℕ) (N : ℕ) (h : A ⊆ Finset.Icc 1 N) :
    A.sum id ≤ A.card * N := by
  calc A.sum id = ∑ a ∈ A, a := rfl
    _ ≤ ∑ _ ∈ A, N := by
        apply sum_le_sum
        intro a ha
        have hacc : a ∈ Finset.Icc 1 N := h ha
        simp only [mem_Icc] at hacc
        exact hacc.2
    _ = A.card * N := by simp [mul_comm]

/-- Pigeonhole bound: if sum-distinct then 2^n ≤ nN + 1 -/
theorem pigeonhole_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    2^A.card ≤ A.card * N + 1 := by
  -- Sum-distinct means 2^n distinct values in [0, sum A] ⊆ [0, nN]
  have hdist := sum_distinct_uniform_distribution A N h
  have hrange : A.sum id ≤ A.card * N := sum_le_card_mul_N A N h.1
  -- Number of possible values is at most nN + 1 (including 0)
  -- But we have 2^n distinct values
  sorry
where
  sum_distinct_uniform_distribution (A : Finset ℕ) (N : ℕ)
      (h : IsSumDistinctSet A N) :
      (A.powerset.image (fun S => S.sum id)).card = 2^A.card := by
    rw [card_image_of_injective]
    · exact card_powerset A
    · intro S hS T hT heq
      have := h.2 ⟨S, hS⟩ ⟨T, hT⟩ heq
      simp only [Subtype.mk.injEq] at this
      exact this

/-- Corollary: N ≥ (2^n - 1) / n -/
theorem N_lower_bound_pigeonhole (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) (hN : 0 < N) :
    (2^A.card - 1 : ℝ) / A.card ≤ N := by
  have hpig := pigeonhole_bound A N h hcard
  -- From 2^n ≤ nN + 1, get N ≥ (2^n - 1) / n
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- PROBABILISTIC METHOD
-- ══════════════════════════════════════════════════════════════════════════════

/-- Expected number of collisions in random subset sums -/
-- For random A ⊆ [1,N] of size n, expected collision count depends on variance
theorem expected_collisions (N n : ℕ) (hn : n ≤ N) :
    ∃ (E_collisions : ℝ), E_collisions ≤ 2^(2*n) / (n * N^2 : ℝ) := by
  -- Each pair of subsets has probability ~1/(nN) of collision
  -- There are (2^n choose 2) pairs
  sorry

/-- Probabilistic existence: there exist sum-distinct sets of size ~log N -/
theorem probabilistic_existence (N : ℕ) (hN : 2 ≤ N) :
    ∃ (A : Finset ℕ) (n : ℕ), A.card = n ∧ IsSumDistinctSet A N ∧
    n ≥ Real.log N / Real.log 2 - Real.log (Real.log N) := by
  -- Random subset of appropriate size has positive probability of being sum-distinct
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- REFINED COUNTING
-- ══════════════════════════════════════════════════════════════════════════════

/-- Second moment method for collisions -/
lemma second_moment_collision (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    ∑ k ∈ Finset.range (A.sum id + 1),
      ((A.powerset.filter (fun S => S.sum id = k)).card : ℝ)^2 = 2^A.card := by
  -- For sum-distinct, each count is 0 or 1, so count² = count
  sorry

/-- The main variance identity gives the Erdős-Moser bound -/
theorem erdos_moser_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (1/4 : ℝ) * 2^A.card / Real.sqrt A.card ≤ N := by
  -- From Σa² ≥ (4^n - 1)/3 and Σa² ≤ n·N²
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- The proven Erdős-Moser bound (1956): N ≥ (1/√3 - o(1))·2^n/√n -/
theorem lb_variance : ∃ (o : ℕ → ℝ),
    (∀ᶠ n in Filter.atTop, |o n| ≤ 1/n) ∧
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1/Real.sqrt 3 - o A.card) * 2^A.card / Real.sqrt A.card ≤ N := by
  sorry

/-- Target: The Elkies-Gleason bound with √(2/π) constant -/
theorem lb_strong : ∃ (o : ℕ → ℝ) (_ : o =o[Filter.atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (Real.sqrt (2 / Real.pi) - o A.card) * 2^A.card / Real.sqrt A.card ≤ N := by
  sorry

/-- Ultimate goal: The $500 Erdős conjecture -/
theorem erdos_1 : ∃ (C : ℝ) (hC : C > 0),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      C * 2^A.card ≤ N := by
  -- Gap from current bound: factor of √n
  sorry

end Erdos1Sidon
