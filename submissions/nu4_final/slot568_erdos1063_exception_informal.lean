/-!
# Erdős Problem 1063: Binomial divisibility — at least one exception always exists

For n ≥ 2k with k ≥ 2, at least one of the integers n-i (0 ≤ i < k) does NOT divide C(n,k).

PROVIDED SOLUTION (Erdős-Selfridge 1983):
We prove by contradiction. Suppose all n-i for i = 0,...,k-1 divide C(n,k).

C(n,k) = n(n-1)(n-2)···(n-k+1) / k!

Since each (n-i) divides C(n,k), and C(n,k) = ∏_{i=0}^{k-1} (n-i) / k!, we have
each (n-i) | ∏_{j=0}^{k-1} (n-j) / k!.

Key observation: Consider the prime factorization. Let p be any prime ≤ k.
The p-adic valuation of k! is v_p(k!) = ∑_{j≥1} ⌊k/p^j⌋ (Legendre's formula).
The p-adic valuation of ∏(n-i) for i=0,...,k-1 distributes among the k consecutive
terms n, n-1, ..., n-k+1.

The argument proceeds via Kummer's theorem: v_p(C(n,k)) equals the number of
carries when adding k and n-k in base p.

Now, among n, n-1, ..., n-k+1, the largest power of p dividing any single (n-i)
contributes at most v_p(n-i) to the p-adic valuation of the product.

If every (n-i) divides C(n,k), then v_p(n-i) ≤ v_p(C(n,k)) for every i and every prime p.
But ∑_{i=0}^{k-1} v_p(n-i) = v_p(∏(n-i)) = v_p(k! · C(n,k)) = v_p(k!) + v_p(C(n,k)).

So ∑ v_p(n-i) = v_p(k!) + v_p(C(n,k)) ≥ k · v_p(C(n,k)) if each v_p(n-i) ≤ v_p(C(n,k)).
Wait — the constraint is each v_p(n-i) ≤ v_p(C(n,k)), so ∑ v_p(n-i) ≤ k · v_p(C(n,k)).
But ∑ v_p(n-i) = v_p(k!) + v_p(C(n,k)).
So v_p(k!) + v_p(C(n,k)) ≤ k · v_p(C(n,k)), giving v_p(k!) ≤ (k-1) · v_p(C(n,k)).

For p = 2 and k ≥ 2: v_2(k!) ≥ k - s_2(k) (where s_2 is the digit sum in base 2),
and we need (k-1) · v_2(C(n,k)) ≥ v_2(k!).

For n = 2k (the minimal case), C(2k,k) = (2k)!/(k!)² and v_2(C(2k,k)) = s_2(k)
(by Kummer's theorem: carries when adding k+k in base 2 = number of 1-bits in k).

So (k-1) · s_2(k) ≥ k - s_2(k), giving k · s_2(k) ≥ k, so s_2(k) ≥ 1 which is always
true. This doesn't immediately give contradiction for n = 2k.

For general n ≥ 2k, the argument uses the Chinese Remainder Theorem and the pigeonhole
principle: among k consecutive integers n, n-1, ..., n-k+1, the distribution of prime
factors is constrained. Taking p as the largest prime ≤ k gives a contradiction because
the p-adic valuation of C(n,k) is too small to accommodate all k divisibility requirements.

Specifically, by Bertrand's postulate, there exists a prime p with k/2 < p ≤ k.
Then among n, n-1, ..., n-k+1 there are at most 2 multiples of p (since the range
has length k < 2p). The p-adic valuation contributed by these ≤ 2 multiples must
account for all of v_p(k!) + v_p(C(n,k)), but v_p(k!) ≥ 1 and each (n-i) divisible
by p contributes at most v_p(n-i), which if it must be ≤ v_p(C(n,k)), constrains
the total. For k ≥ 2, this forces v_p(C(n,k)) = 0 for some choices but also
forces at least one (n-i) to have v_p(n-i) > v_p(C(n,k)).

Reference: Erdős, P. and Selfridge, J.L., Problem 6447, Amer. Math. Monthly (1983), 710.

Key Mathlib lemmas:
- `Nat.choose`: binomial coefficient
- `Nat.multiplicity_choose`: p-adic valuation of C(n,k)
- `Nat.Prime.dvd_choose_prime`: prime divisibility of binomials
- `Nat.exists_prime_and_dvd`: Bertrand's postulate
-/

import Mathlib

namespace Erdos1063

theorem erdos_1063_exists_exception {n k : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k := by
  sorry

end Erdos1063
