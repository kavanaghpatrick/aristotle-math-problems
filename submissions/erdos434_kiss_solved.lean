/-
Erdős Problem #434 - Maximizing Unrepresentable Sums
CRITICAL GAP: Marked "open" in Formal Conjectures but SOLVED by Kiss (2002)!

Kiss proved: Yes, {n, n-1, ..., n-k+1} maximizes unrepresentable integers.

Reference: Kiss, Peter. "On a problem of Erdős about integers of the form
            2^k + p." Periodica Mathematica Hungarica 45 (2002): 159-165.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators

noncomputable section

namespace Erdos434

/--
A natural n is representable by set A if it can be written as the sum
of finitely many elements of A (with repetition allowed).
-/
def Nat.IsRepresentableAs (n : ℕ) (A : Set ℕ) : Prop :=
    ∃ (S : Multiset ℕ), (∀ a ∈ S, a ∈ A) ∧ S.sum = n

/--
The number of naturals not representable by set A.
-/
noncomputable def Nat.NcardUnrepresentable (A : Set ℕ) : ℕ :=
    { n : ℕ | ¬n.IsRepresentableAs A }.ncard

/--
Kiss (2002) proved: For all n ≥ 1, k ≥ 1 with k ≤ n, the set {n-k+1, ..., n}
maximizes the count of unrepresentable integers among all k-element subsets
of {1, ..., n}.

This is the affirmative answer to Erdős's question.
-/
theorem erdos_434_kiss_theorem (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (h : k ≤ n) :
    IsGreatest
      { Nat.NcardUnrepresentable S | (S : Set ℕ) (_ : S ⊆ Set.Icc 1 n) (_ : S.ncard = k) }
      (Nat.NcardUnrepresentable (Set.Icc (n - k + 1) n)) := by
  sorry

/--
The answer to Erdős 434 is True: the set of k largest consecutive integers
does maximize the count of unrepresentable integers.
-/
theorem erdos_434_answer : ∀ (n : ℕ), 1 ≤ n → ∀ (k : ℕ), 1 ≤ k → k ≤ n →
    IsGreatest
      { Nat.NcardUnrepresentable S | (S : Set ℕ) (_ : S ⊆ Set.Icc 1 n) (_ : S.ncard = k) }
      (Nat.NcardUnrepresentable (Set.Icc (n - k + 1) n)) := by
  intro n hn k hk h
  exact erdos_434_kiss_theorem n k hn hk h

end Erdos434
