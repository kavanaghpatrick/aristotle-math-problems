/-
slot301: Prove max(A) ≥ C(n-1, ⌊(n-1)/2⌋) for sum-distinct sets

This is the KEY LEMMA for lb_strong. From Dubroff-Fox-Xu (2021).

STATEMENT: If A is sum-distinct with |A| = n, then max(A) ≥ C(n-1, ⌊(n-1)/2⌋).

PROOF IDEA:
Let a = max(A) and B = A \ {a}.
Consider the bijection φ : 2^B → 2^B sending S ↦ (A.sum - a - S.sum) mod something...

Actually, simpler approach:
- There are C(n-1, k) subsets of B with k elements
- The middle layer has C(n-1, ⌊(n-1)/2⌋) elements
- By a clever counting argument, a ≥ C(n-1, ⌊(n-1)/2⌋)
-/

import Mathlib

open Finset BigOperators

noncomputable section

namespace Erdos1

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- Helpers
lemma sum_distinct_inj (A : Finset ℕ) (h : IsSumDistinctSet A N) :
    Function.Injective (fun S : {S // S ∈ A.powerset} => (S : Finset ℕ).sum id) := h.2

/-- For sum-distinct A, subset sums are all different -/
lemma subset_sums_distinct (A : Finset ℕ) (h : IsSumDistinctSet A N)
    (S T : Finset ℕ) (hS : S ⊆ A) (hT : T ⊆ A) (hsum : S.sum id = T.sum id) :
    S = T := by
  have := @h.2 ⟨S, mem_powerset.mpr hS⟩ ⟨T, mem_powerset.mpr hT⟩
  simp at this
  exact this hsum

-- ══════════════════════════════════════════════════════════════════════════════
-- THE KEY LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/--
For a sum-distinct set A with |A| = n ≥ 1, max(A) ≥ C(n-1, ⌊(n-1)/2⌋).

Proof sketch (Dubroff-Fox-Xu):
Let a = max(A), B = A \ {a}, and m = (n-1)/2.

Define an injection from the "middle layer" of 2^B to [1, a-1]:
  For S ⊆ B with |S| = m, map S to S.sum mod (a-1) + 1... no that's wrong.

Actually, the argument is:
  Consider pairs (S, S ∪ {a}) where S ⊆ B.
  The sums differ by a: (S ∪ {a}).sum = S.sum + a.

  Among subsets of B, consider those with |S| = m.
  Claim: their sums are all distinct (inherited from A being sum-distinct).

  Now, the C(n-1, m) subsets of size m have C(n-1, m) distinct sums.
  These sums are all in [m, (n-1-m)·N] roughly...

  The key insight: if we pair each S with A \ (S ∪ {a}) = B \ S,
  we get sum(S) + sum(B \ S) = sum(B) = sum(A) - a.

  So sum(S) and sum(B \ S) are determined by each other.

  For |S| = m and |B \ S| = (n-1) - m = n - 1 - m,
  when n is even, m = (n-1)/2 = (n-2)/2 = n/2 - 1, so |B \ S| = n - 1 - (n/2 - 1) = n/2.
  When n is odd, m = (n-1)/2, |B \ S| = n - 1 - (n-1)/2 = (n-1)/2 = m.

  So when n is odd, we have S and B \ S both of size m, and sum(S) + sum(B \ S) = sum(B).

  This creates a pairing! And from this pairing, we can extract the bound on a.
-/
theorem max_ge_central_binom (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hA : A.Nonempty) :
    A.max' hA ≥ (A.card - 1).choose ((A.card - 1) / 2) := by
  /-
  Let n = |A|, a = max(A), B = A \ {a}.

  Consider the map φ : {S ⊆ B : |S| = (n-1)/2} → ℕ given by φ(S) = S.sum.
  By sum-distinctness of A, φ is injective.

  The range of φ is contained in [0, sum(B)] = [0, sum(A) - a].

  But also: for each S with |S| = m = (n-1)/2, we have sum(S) ≥ 0 and sum(S) ≤ sum(B) - something.

  The injectivity of φ on C(n-1, m) elements means the range has ≥ C(n-1, m) elements.

  The range is a subset of [0, sum(A) - a].

  Hmm, this doesn't directly give a ≥ C(n-1, m)...

  The actual Dubroff-Fox-Xu argument uses a more sophisticated bijection involving
  the "complement" operation S ↦ B \ S and properties of Sperner's theorem / LYM inequality.

  Let me try a different approach: use the fact that among 2^(n-1) subsets of B,
  at most C(n-1, m) can have sum < a (by an antichain argument).

  Actually, here's a cleaner argument:
  The 2^(n-1) subsets of B have 2^(n-1) distinct sums (inherited from A).
  The 2^(n-1) subsets of A containing 'a' are {S ∪ {a} : S ⊆ B}.
  Their sums are {S.sum + a : S ⊆ B}.

  For these 2^n sums to all be distinct:
  - The 2^(n-1) sums from B must be distinct (automatic)
  - The 2^(n-1) sums from {S ∪ {a}} must be distinct (automatic, shifted by a)
  - These two sets of 2^(n-1) sums must be disjoint!

  The first set is {S.sum : S ⊆ B} ⊆ [0, sum(B)].
  The second set is {S.sum + a : S ⊆ B} ⊆ [a, sum(B) + a].

  For disjointness, we need: max{S.sum : S ⊆ B} < min{S.sum + a : S ⊆ B}.
  I.e., sum(B) < 0 + a, i.e., sum(B) < a.

  But sum(B) = sum(A) - a ≥ 1 + 2 + ... + (n-1) - a = n(n-1)/2 - a for the minimum case.

  Hmm, this gives a > sum(B), not a ≥ C(n-1, m).

  I think the actual argument requires the LYM/antichain structure.
  -/
  sorry

end Erdos1

end
