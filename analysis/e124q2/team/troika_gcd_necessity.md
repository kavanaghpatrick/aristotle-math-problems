# troika: Why gcd(D)=1 is necessary for k≥1 (and not for k=0) — COMPLETE

## Result (fully proven, computationally confirmed)

The gcd(D)=1 hypothesis in `erdos124.ne_zero` is **necessary and the mechanism is elementary**.

### Key structural identity
For any d, k:
```
sumsOfDistinctPowers(d, k) = d^k · sumsOfDistinctPowers(d, 0)
```
i.e. = { d^k · a : a is a 0-1-digit number in base d }. Every element is a multiple of d^k.
(Proof: ∑_{i∈s, i≥k} d^i = d^k · ∑_{i∈s} d^{i-k}, and {i-k : i∈s} is an arbitrary finite subset of ℕ.)

### Necessity of gcd=1 for k≥1
Let g = gcd(D) and suppose g > 1. For each d ∈ D and k ≥ 1:
  g | d  ⟹  g | d^k  ⟹  every element of sumsOfDistinctPowers(d,k) ≡ 0 (mod g).
Therefore every element of the pointwise sumset ∑_{d∈D} sumsOfDistinctPowers(d,k) ≡ 0 (mod g).
**No integer n with n ≢ 0 (mod g) is ever representable.** Since there are infinitely many such n,
the "∀ᶠ n, n ∈ sumset" conclusion FAILS. The conjecture is false without gcd=1. ∎

### Why k=0 escapes
For k=0, sumsOfDistinctPowers(d,0) contains d^0 = 1 (the singleton {0} power). So `1` is in each
component set, and the confinement argument breaks: the term need not be ≡ 0 mod g. Indeed the k=0
statement (erdos124.zero) has NO gcd hypothesis and is TRUE (Alexeev/Aristotle, Nov 2025).

### Computational confirmation
- Built explicit gcd>1 density-admissible families:
  - D=(4,6,8,10,12,14,16), gcd 2, ∑1/(d-1)=1.0218: at k=1, of 60000 odd numbers below 120000,
    **exactly 0 are covered**; only even numbers (1 small exception, n=2) covered.
  - D=(3,6,9,12,15,18), gcd 3, ∑1/(d-1)=1.0462: at k=1, of 80000 non-multiples-of-3 below 120000,
    **exactly 0 covered**; ALL multiples of 3 covered (threshold 0).
- Such families exist for every g (max density with all d multiples of g, d≥3:
  g=2→3.78, g=3→2.97, g=4→2.17, g=5→1.71, g=6→1.42, g=7→1.21 — all ≥1). So the gcd
  hypothesis is non-vacuous: density-admissible gcd>1 families exist and all fail.

## Consequence for the proof strategy
The REAL content of erdos124.ne_zero is the **sufficiency** direction with gcd=1:
  gcd(D)=1 + density≥1  ⟹  ∀ᶠ n, n representable.
The gcd condition is what lets the bases "cooperate mod m" for every modulus m — the analogue of
the carry/covering argument that works automatically at k=0 (where the digit-1 terms generate
everything mod anything).

See troika_scaling.md for the d^k scaling structure and the (3,4,7) reverse-engineering.
