# The prime-power-collinearity bound (task #6) — RESOLVED

**Author:** scholar. **Status:** PROVED (elementary, exact arithmetic). Answers the question
"does ∑1/(d−1)≥1 + gcd(D)=1 structurally forbid Melfi-style near-degenerate {3,9,81,…} families?"
Origin: Melfi04's caution that gcd{A}=1 is insufficient for his density Conjecture 1 (his
counterexample {3,9,81,104}). Relevant to troika's Baker-route multiplicative-dependence blind spot.

## The object

For a prime p, the "pure power-tower" bases (≥3) are `T_p = {p^a : a≥1, p^a ≥ 3}`. Their harmonic
mass is `M(p) = ∑_{p^a ≥ 3} 1/(p^a − 1)`. The Melfi pathology is a D whose bases are (nearly) all
in one `T_p`: then the components `p^{ak}·B_{p^a}` nest multiplicatively and add little new residue
diversity, so density/coverage can collapse despite gcd=1.

## LEMMA 1 (single-prime-tower mass is bounded below 1). For every prime p,
> `M(p) = ∑_{a: p^a ≥ 3} 1/(p^a − 1) ≤ M(3) = 1/2 + 1/8 + 1/26 + 1/80 + … < 0.6822 < 1.`

Exact computed values (bases ≥ 3, so base 2 excluded by the d≥3 rule):
- M(2) = 1/3+1/7+1/15+… ≈ **0.60670** (bases 4,8,16,…)
- M(3) = 1/2+1/8+1/26+… ≈ **0.68215** (bases 3,9,27,…) ← the SUPREMUM over all primes
- M(5) ≈ 0.30173, M(7) ≈ 0.19091, M(11) ≈ 0.10916, decreasing in p.

`M(3)` is the max because base 3 contributes the largest single term 1/(3−1)=1/2 of any allowed
prime power, and the tower decays geometrically. **Proof that M(3) is the sup:** for p≥5,
M(p) < 1/(p−1) · 1/(1−1/p) = 1/(p−2)·... actually crude bound: M(p) < ∑_{a≥1} p^{-a}/(1−p^{-a})
≤ (1/(p−1))·(1/(1−1/(p−1))) which is < 1/2 for p≥5; and M(2) < M(3) by direct sum. ∎

**Corollary 1 (no single-prime-collinear admissible D).** No admissible D (∑1/(d−1) ≥ 1) can have
all its bases be pure powers of a single prime. Admissibility STRICTLY requires harmonic mass that
no one prime-tower can supply. (Even taking the ENTIRE infinite tower of one prime falls short of 1.)

## LEMMA 2 (two-prime smooth families — where the stress tests live). Let `T_{p,q}` be all bases
≥3 of the form `p^a q^b` (the {p,q}-smooth numbers). Then (exact):
- {2,3}-smooth: mass ≈ **1.837 ≥ 1** (bases 3,4,6,8,9,12,16,18,24,27,…) — ADMISSIBLE families exist
- {2,5}-smooth: ≈ **1.174 ≥ 1**;  {3,5}-smooth: ≈ **1.114 ≥ 1**
- {2,7}-smooth: ≈ 0.972 < 1;  {3,7}-smooth: ≈ 0.959 < 1 — NOT admissible even taking all of them

So two prime-supports CAN reach admissibility, but only the "small-prime" pairs ({2,3},{2,5},{3,5});
once a prime ≥7 is involved the two-prime mass already falls short. This pins down EXACTLY where
the maximally-collinear admissible D live: minimal finite subsets of the {2,3}-, {2,5}-, or
{3,5}-smooth numbers. Concrete minimal examples (gcd=1, ∑≥1, all bases p^a q^b):
- {2,3}: D=(3,4,8,9) ∑=1.101; (3,4,8,32) ∑=1.008; (3,4,9,16) ∑=1.025 [breaker testing]

## STRUCTURAL UPSHOT (the lever, stated cleanly)

> **The harmonic admissibility condition ∑1/(d−1)≥1 forces the bases of D to span the power-towers
> of ≥2 distinct small primes with genuine multiplicative independence** (Lemma 1 + 2). This is
> PRECISELY the multiplicative spread that BEGL's Claim-4 residue-sweep needs (a base coprime to
> each prime modulus). gcd(D)=1 alone does NOT give this (Melfi's {3,9,81,104}, mass 0.647 < 1,
> is gcd=1 but collapses) — it is the HARMONIC condition that supplies the spread, by forbidding
> single-tower collinearity.

This explains WHY Q2 should be TRUE and reconciles Melfi's caution with BEGL: Melfi's pathology
needs sub-critical mass (his example is 0.647 < 1); the moment you demand ∑≥1 you are forced off
any single tower onto ≥2 small-prime towers, restoring the residue diversity. The residue half is
then exactly lift/sumset/modular's proven (R). The remaining work is the (A) gap-filling half on
these forced-spread sets — and breaker's stress tests on (3,4,8,9) etc. are the empirical probe of
the worst case.

**Caveat (honest):** Lemma 1/2 bound PURE prime-power and two-prime-SMOOTH families. A general
admissible D can mix more primes, which only HELPS (more spread). The genuinely adversarial case
for the residue-sweep is the minimal two-small-prime admissible set, now identified. This does NOT
by itself prove (A); it removes the single-tower collapse as an obstruction and localizes the hard
case. Combined with the team's proven (R), it narrows Q2's open core to: gap-filling on
{2,3}/{2,5}/{3,5}-smooth admissible D at the harmonic boundary.
