/-
Erdős Problem #313 - Primary Pseudoperfect Numbers
CONSTRUCTIVE APPROACH

Key insight: The sequence 2, 6, 42, 1806, ... has structure:
- 6 = 2 × 3, where 3 = 2 + 1
- 42 = 6 × 7, where 7 = 2×3 + 1
- 1806 = 42 × 43, where 43 = 2×3×7 + 1

If n is PPP with primes P and (∏P + 1) is prime, then n × (∏P + 1) is PPP.

This gives infinitely many IF there are infinitely many such primes.
(This is related to primorial primes / Euclid-Mullin sequence)
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos313

def erdos_313_solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

def IsPrimaryPseudoperfect (n : ℕ) : Prop := ∃ P, (n, P) ∈ erdos_313_solutions

-- Proven examples
theorem solution_2 : (2, {2}) ∈ erdos_313_solutions := by
  simp [erdos_313_solutions]; norm_num

theorem solution_6 : (6, {2, 3}) ∈ erdos_313_solutions := by
  simp [erdos_313_solutions]
  refine ⟨by norm_num, by simp, ?_, ?_⟩
  · intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num
  · norm_num

theorem solution_42 : (42, {2, 3, 7}) ∈ erdos_313_solutions := by
  simp [erdos_313_solutions]
  refine ⟨by norm_num, by simp, ?_, ?_⟩
  · intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num
  · norm_num

theorem solution_1806 : (1806, {2, 3, 7, 43}) ∈ erdos_313_solutions := by
  simp [erdos_313_solutions]
  refine ⟨by norm_num, by simp, ?_, ?_⟩
  · intro p hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · norm_num

/-
KEY LEMMA: Extension property
If (n, P) is a solution and q = (∏ p∈P) + 1 is prime and q ∉ P,
then (n * q, P ∪ {q}) is also a solution.

Proof sketch:
- Original: ∑(1/p for p∈P) = 1 - 1/n
- Let prod = ∏P, so q = prod + 1
- New sum: ∑(1/p for p∈P) + 1/q = (1 - 1/n) + 1/(prod+1)
- We need: (1 - 1/n) + 1/(prod+1) = 1 - 1/(n*q)
- i.e., 1/(prod+1) = 1/n - 1/(n*q) = (q-1)/(n*q) = prod/(n*q)
- i.e., n*q = prod*(prod+1)
- This holds when n = prod (which is true for the sequence!)
-/
lemma extension_lemma (n : ℕ) (P : Finset ℕ) (h_sol : (n, P) ∈ erdos_313_solutions)
    (h_n_eq_prod : n = ∏ p ∈ P, p)
    (q : ℕ) (h_q_def : q = (∏ p ∈ P, p) + 1) (h_q_prime : q.Prime) (h_q_notin : q ∉ P) :
    (n * q, P ∪ {q}) ∈ erdos_313_solutions := by
  sorry

/-- The sequence a(0)=2, a(n+1)=a(n)*(∏primes(n)+1) when the factor is prime -/
def pppSequence : ℕ → ℕ
  | 0 => 2
  | n + 1 => sorry -- Would need to track the prime set

/-- All elements of the PPP sequence are primary pseudoperfect -/
theorem pppSequence_isPPP (n : ℕ) : IsPrimaryPseudoperfect (pppSequence n) := by
  sorry

/-- MAIN THEOREM: Infinitely many PPPs exist
    (Conditional on infinitely many primorial+1 primes) -/
theorem erdos_313_infinite : Set.Infinite {n | IsPrimaryPseudoperfect n} := by
  sorry

end Erdos313
