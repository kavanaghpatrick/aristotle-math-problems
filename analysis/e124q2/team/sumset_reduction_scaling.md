# E124 open part: the scaling reduction S(d,k) = d^k · S(d,0)

**Author:** sumset. **Status:** PROVED (one line), computationally confirmed.

## Notation

Write `S(d,k) := sumsOfDistinctPowers d k = { ∑_{i∈s} d^i : s ⊂ ℕ finite, ∀i∈s, i≥k }`.
Note `0 ∈ S(d,k)` for all k (empty Finset). Write `B_d := S(d,0)` = "numbers with only digits 0/1 in base d".

## Lemma (scaling). For all d, k ≥ 0:  `S(d,k) = d^k · B_d`  (Minkowski scaling of the set).

**Proof.** Let x ∈ S(d,k), so x = ∑_{i∈s} d^i with every i ≥ k. Define the Finset
s' := s.map (· - k) = { i - k : i ∈ s }. Since the map j ↦ j - k restricted to {i : i ≥ k}
is injective (it's `(· + k)`-invertible there), |s'| = |s| and
  ∑_{i∈s} d^i = ∑_{i∈s} d^k · d^{i-k} = d^k · ∑_{j∈s'} d^j = d^k · (element of B_d).
Conversely if y = ∑_{j∈s'} d^j ∈ B_d, then s := s'.map (· + k) has all elements ≥ k and
∑_{i∈s} d^i = d^k · y. ∎

The Lean-level statement is `S d k = (d^k) • B_d` (pointwise scalar mul of a `Set ℕ`), or
`x ∈ S d k ↔ d^k ∣ x ∧ x / d^k ∈ B_d`. Computationally confirmed for d∈{3,4,5,7}, k∈{1,2,3}.

## Consequence: restated open problem

The pointwise sumset over D becomes
  `∑_{d∈D} S(d,k) = ∑_{d∈D} d^k · B_d`.

So the BEGL96 open question is exactly:

> **(Q)** For every k ≥ 1 and every admissible D (all d ≥ 3, ∑ 1/(d−1) ≥ 1, gcd(D)=1),
> is `∑_{d∈D} d^k · B_d` cofinite in ℕ?

with the k=0 theorem (Alexeev/Aristotle) giving: `∑_{d∈D} B_d` is cofinite whenever
all d ≥ 3 and ∑ 1/(d−1) ≥ 1 (NO gcd condition needed at k=0).

## Why gcd(D)=1 is forced when k ≥ 1 (sanity check — PROVED)

Every element of d^k·B_d is divisible by d^k. If g := gcd(D) > 1, pick a prime p | g.
Then p | d for every d ∈ D, so p^k | d^k | every a_d, hence p^k divides every element of
∑_{d∈D} d^k·B_d. A cofinite set cannot be contained in p^k·ℕ (it omits, e.g., p^k·m + 1 for
large m). So cofiniteness FAILS whenever gcd(D) > 1 and k ≥ 1. This is exactly why BEGL96 adds
gcd(D)=1 for k ≥ 1, and why k=0 needs no such condition (d^0 = 1).

**Caveat / subtlety:** gcd(D)=1 is NECESSARY but the converse-direction (Pomerance) density bound
∑ 1/(d−1) ≥ 1 is ALSO necessary and is unaffected by k (scaling B_d by d^k doesn't change its
density 1/(d−1) as a multiplicative factor on counting — see density file). So the two side
conditions (∑1/(d−1)≥1 AND gcd=1) are the two independent obstructions; (Q) asks if they suffice.

## The reduction does NOT trivially follow from k=0

Tempting wrong move: "∑ d^k·B_d ⊇ d_min^k · (∑ B_d) so apply k=0 and scale." FALSE — the sumset
of scaled sets is NOT a scaling of the sumset unless all scale factors are equal. Here the factors
d^k differ across d (since the d differ), so ∑_{d∈D} d^k·B_d is a genuinely new object. The gcd=1
condition is precisely what couples the differing scale factors d^k via CRT. See sumset_crt_*.md.
