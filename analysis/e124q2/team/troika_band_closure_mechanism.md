# troika: the band-closure mechanism — exactly how/why MW enters (the lead's question, answered)

This is the precise reconstruction of how the BEGL96 (3,4,7) induction bottoms out, and the clean
statement of what must be generalized. All verified computationally. Builds on
[[troika_generalization_mechanism]], [[maverick_bounded_gap_lemma]], [[breaker_engine_and_347anomaly]].

## The exceptional integers live in thin bands just below base-powers
For (3,4,7) k=2, the largest exceptionals each sit in a narrow band [d^e / 1.07, d^e) below a power:
| exceptional | nearest power above | ratio (power/exc) |
|---|---|---|
| 254302 | 4^9 = 262144 | 1.031 |
| 516446 | 3^12 = 531441 | 1.029 |
| 785743 | 7^7 = 823543 | 1.048 |
| 3982888 | 4^11 = 4194304 | 1.053 |
The bands recur under powers of ALL three bases (not just the largest), and THIN OUT as the exponent
grows (4^9 band: 4 exceptionals; 4^11 band: 2; 4^12+ bands: empty). N₀ is the top of the last
nonempty band.

## Why these n are hard (the bottoming-out)
An integer n in [d^e / r, d^e) is too large to represent without using a power near d^e, yet the
power d^e itself overshoots. So n must be built entirely from atoms STRICTLY BELOW d^e (across all
bases). Representability then hinges on whether those smaller atoms can hit n exactly.

## It is a GRANULARITY failure, not a density failure (decisive computation)
For the band below 4^11 = 4194304 (k=2): the total sum of all atoms < 4194304 is **4 750 368**,
which EXCEEDS the exceptional 3 982 888 by a headroom of 767 480. So there is NO density deficit —
the available mass is more than enough (consistent with maverick's Lemma BG: long runs are
impossible). Yet 3 982 888 is provably unreachable (3 independent engines). **The obstruction is
GRANULARITY**: the achievable subset-sums near n skip this specific value. Near a power boundary the
spacing between consecutive achievable sums is controlled by how the second-tier powers of the
DIFFERENT bases interleave — i.e. by |dᵢ^p − dⱼ^q|. **That spacing is exactly what Mignotte–
Waldschmidt linear forms in logs bound, and it is why elementary density (Cassels/Lemma BG) cannot
finish.** (Confirmed separately in [[troika_cassels_insufficient]]: the naive Cassels bound
underestimates N₀ by 200×–29000×.)

## The clean split (final, reconciled team picture)
1. **Long-run prevention** = elementary, k-uniform: total atom-mass dominates (maverick's Lemma BG,
   powered by ∑1/(d−1) ≥ 1). Bounds the max RUN of consecutive missing by ~d_min^k. Formalizer-reachable.
2. **Granularity / isolated-point elimination at the power-boundary bands** = the genuine open core.
   Needs Baker/MW lower bounds on |dᵢ^p − dⱼ^q| to show each band closes (no isolated point survives
   above N₀). Not in Mathlib; not bare-submittable. BEGL96 did this BY HAND only for (3,4,7), s=1.

## Generalization status (my lane)
- **Always-available tool:** every admissible D has a multiplicatively-independent base pair (my
  Lemma, [[troika_generalization_mechanism]]) — so an MW bound always has a target.
- **What must be generalized:** (a) an EFFECTIVE MW bound on |a^p − b^q| for the dominant indep pair
  with explicit constants; (b) a band-closure argument showing the remaining bases fill each
  power-boundary band's granularity gaps. Both are met structurally; the quantitative effective
  version for arbitrary D is open (the regime BEGL call themselves "fairly far from").
- **Honest verdict:** the conjecture is TRUE (overwhelming evidence), the mechanism is fully
  identified (power-boundary band granularity, closed by MW), but no elementary or bare-submittable
  closure exists. The one rigorously-closed instance remains BEGL96's (3,4,7), s=1, largest gap 581.
