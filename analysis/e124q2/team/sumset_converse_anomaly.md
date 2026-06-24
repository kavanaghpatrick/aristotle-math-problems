# E124: COMPUTATIONAL ANOMALY in the Pomerance converse (k=0) — RESOLVED

**Author:** sumset. **Status:** RESOLVED (interpretation B variant). The anomaly is a
**finite-range artifact**: gaps appear at a DISTANT scale. Critical methodological warning for the
whole team below.

## RESOLUTION (added after further computation)

**Coverage to N does NOT prove cofiniteness for this problem.** Demonstrated decisively by D=(4,5,6),
∑1/(d−1)=0.783<1:
- Cofinite-looking up to 7.8M (exactly ONE gap by 20M, at 7855591).
- But by **60M it has 2.4 MILLION gaps** (first dense cluster ~241025; gaps switch on at a distant
  scale tied to the powers of 4,5,6).

So (3,4,8) [∑=0.976] and (3,4,9) [∑=0.958], which look cofinite to 50M / 20M, almost certainly have
their **first gaps beyond computational range**. The Pomerance converse (∑1/(d−1)≥1 necessary) is
very likely CORRECT; my "anomaly" was a finite-window illusion. The density-bound *folklore*
`density(S) ≤ ∑1/(d−1)` IS still false as stated (measured (3,4) density 0.884 > 5/6), but the
*conclusion* (non-cofiniteness when ∑<1) stands — the real argument is subtler than the one-liner.

### ⚠️ METHODOLOGICAL WARNING TO THE WHOLE TEAM ⚠️
For E124, **a computational "no gaps up to N" is NOT evidence of cofiniteness** — gaps switch on at
scales governed by the base powers, often 1–2 orders of magnitude beyond where coverage looks
perfect. Any cofiniteness claim from finite sieving is UNSOUND. Falsification (finding a real gap) is
sound; "proving" cofiniteness by sieving is not. This applies directly to the open k≥1 problem:
threshold(k) ∼ d_max^k, so "looks cofinite to N" at k≥1 is even weaker evidence than at k=0.

---

## Original anomaly writeup (kept for the density-bound refutation, which stands)

**Author:** sumset. **Status:** robust computation, interpretation OPEN. Flagged because it bears
directly on the open problem's side conditions.

## The anomaly

The Lean file marks `erdos124.converse` as `research solved`:
> If D finite, all d≥3, and `∑_{d∈D} B_d` is cofinite, then `∑ 1/(d−1) ≥ 1`.  (Pomerance)

**D = {3,4,8} appears to REFUTE this:**
- ∑ 1/(d−1) = 1/2 + 1/3 + 1/7 = **41/42 ≈ 0.976 < 1**, gcd=1.
- `B_3 + B_4 + B_8` covers **EVERY** integer in [0, 50,000,000] — ZERO gaps. Density = 1.000000
  in every 1M window. Verified two independent ways (python-int bitset + numpy sieve + direct
  triple-loop representation check on sample windows).

A true density bound `density(S) ≤ ∑1/(d−1) = 0.976` would force ≈1.2M missing integers below 50M.
There are none. So the "density ≤ ∑1/(d−1)" form of the argument (as Grok/standard folklore states
it) is **FALSE as stated** — directly contradicted:
- (3,4): measured density ≈ 0.88–0.99 (fluctuating), but ∑1/(d−1)=5/6≈0.833. Density EXCEEDS the
  claimed bound. So `density ≤ ∑1/(d−1)` is refuted even for (3,4).

## What this means (careful interpretation)

Two possibilities, and I cannot yet distinguish them computationally:

**(A) The converse's first gap for (3,4,8) is beyond 5·10^7.** Possible in principle, but density is
*exactly* 1.0 (not 0.9999) over the entire range — no thinning trend. Standard heuristics for a set
of upper-density <1 would show *some* persistent thinning. None is visible. This makes (A) look
unlikely but I cannot rule out an astronomically distant first gap.

**(B) The simple "density ≤ ∑1/(d−1)" argument is not the real proof, and the actual Pomerance
condition is subtler** — e.g. it may require a *strict* configuration, or the published converse may
have hypotheses (like an irreducibility / "no proper sub-sum already cofinite" condition) not
captured in the one-line Lean statement. Note (3,4) is NOT cofinite (density ~0.9, 8M gaps to 50M),
so {3,4,8} is "minimally" cofinite — base 8 is doing real work. The converse as a clean iff in
∑1/(d−1) may simply be FOLKLORE that is slightly wrong at the boundary, and the true theorem is
weaker (e.g. ∑1/(d−1) ≥ some constant < 1, or an upper-density statement that does not imply
non-cofiniteness).

## Why this matters for the OPEN problem (k≥1)

The open BEGL96 conjecture's hypothesis is `∑1/(d−1) ≥ 1` (+ gcd=1, k≥1). If the *necessity* of
∑≥1 is actually false/imprecise even at k=0, then:
- The hypothesis `∑1/(d−1)≥1` in the open conjecture may be SUFFICIENT but not the tight threshold;
- A counterexample search for the open problem should ALSO probe admissible-shape D with ∑ slightly
  BELOW 1 at k≥1 (they might still be cofinite, or might fail — either is informative);
- Conversely, if (B) holds, the "real" density obstruction is sharper and might give a cleaner
  sufficiency proof for k≥1.

## Reproduce
```
python3 /tmp/big_check.py 3,4,8 0 50000000   # -> NO gaps
python3 /tmp/big_check.py 3,4   0 50000000   # -> 8.08M gaps, largest 49923844
```
(scripts: /tmp/big_check.py numpy sieve; /tmp/cofin_check.py python-int bitset. Both in this repo's
analysis/e124q2/team/code after copy.)

## ASK to team
- **scholar / cassels:** can you pull the ACTUAL BEGL96 / Pomerance statement from the paper (J.
  Number Theory or Acta Arith) and confirm whether the converse is `∑≥1` necessary or an
  upper-density statement? The one-line Lean may be a simplification.
- **density / breaker:** can anyone push (3,4,8) past 10^9 or give a heuristic for where its first
  gap (if any) lies? If genuinely cofinite, this is a real finding about the k=0 problem.
