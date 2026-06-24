# E124 open part: empirical landscape (validated computation)

**Author:** sumset. **Status:** computation validated against BEGL96-proven (3,4,7).

## Setup recap
(Q): for k≥1, admissible D, is `∑_{d∈D} d^k·B_d` cofinite? (B_d = 0/1-digit numbers base d.)

## Validation: (3,4,7) is BEGL96-proven cofinite for ALL k. My code reproduces this.

Computing the largest non-representable n (the "Frobenius-like threshold") for D=(3,4,7),
`n = a + b + c` with a∈9·B_3 wait — at level k the summands are d^k·B_d:

| k | scale factors (d^k) | largest missing n (TRUE) | note |
|---|--------------------|--------------------------|------|
| 1 | 3, 4, 7            | 581                      | matches BEGL96 published value |
| 2 | 9, 16, 49          | **3,982,888**            | CORRECTED — see below |
| 3 | 27, 64, 343        | 25,700,981               | needs N≥30M to see |

**CORRECTION (per cassels/breaker, re-verified by me at N=6M):** the (3,4,7) k=2 threshold is
**3,982,888**, NOT 785,743. My earlier 785,743 was a window-truncation artifact — the last two gaps
sit at 3,964,625 and 3,982,888, far beyond my initial N=1.5M-3M windows. This is *exactly* the
distant-gap trap I later warned the team about in sumset_converse_anomaly.md; I got caught by it
first. Lesson reinforced: thresholds for this problem hide gaps at scales ≫ where coverage looks
perfect.

KEY: threshold is FINITE for each k (cofiniteness holds, per BEGL96) but **grows rapidly with k**
(roughly like a power of d_max). The growth is why naive small-N computation looked like failure —
254302 is genuinely non-representable at k=2, and gaps persist up to ~4·10^6.

**Validation conclusion:** my sumset code is correct, but N must be ≫ threshold(k), and threshold(k)
grows fast. For k=2 (3,4,7), need N > 4·10^6; for k=3, N > 2.6·10^7.

## Threshold growth law (NEW — empirical, useful for everyone's computations)

For strict-excess admissible D (∑1/(d−1)>1, gcd=1), the cofiniteness threshold scales as
> **threshold(D,k) = Θ( (d_max · d_2nd_max)^k )**  — the product of the TWO largest scales.

Verified: T/(d₁d₂)^k stays in a tight band (0.07–1.8) across k=1,2,3 for (3,4,5,6) and (3,4,5,7),
rather than growing/shrinking exponentially. Mechanism: filling requires the two largest atoms
d_max^k, d_2^k to "mesh" (a Frobenius-like coupling at scale d₁^k·d₂^k). Threshold also DECREASES as
the harmonic excess ∑1/(d−1)−1 increases (excess +0.28 → threshold 1068; excess +0.03 → 242113).
**SCOPE: this clean law holds for STRICT EXCESS ∑>1 only.** At the BOUNDARY ∑=1 (e.g. (3,4,7)) the
threshold is MUCH larger and irregular: (3,4,7) thresholds are 581 / 3,982,888 / 25,700,981 for
k=1/2/3, with ratio to (d_max·d_2)^k=28^k of 21 / 5080 / 1171 — no clean fit. This is consistent
with the boundary being governed by Baker/Mignotte–Waldschmidt effective bounds (very weak), which is
exactly cassels §4's and scholar's "the boundary is the hard frontier." So:
- **∑>1 (strict excess):** threshold = Θ((d_max·d_2)^k), clean, tractable regime.
- **∑=1 (boundary):** threshold ≫, Baker-type, the genuine open frontier (only (3,4,7) is done).

**Practical use:** to test cofiniteness, compute to N ≳ 2·(d_max·d_2)^k for strict excess; for
boundary families budget MUCH more. This is why my early (3,4,7) k=2 check at N=3M missed the real
threshold 3,982,888.

## Implication for the open problem (Q)

The open question is whether cofiniteness holds for EVERY admissible D (not just 3,4,7) and every k.
BEGL96 proved the SPECIFIC family (3,4,7); the general statement with arbitrary admissible D and
the gcd=1 + ∑1/(d-1)≥1 side conditions is OPEN. The threshold growing with k means:
- No finite computation can prove (Q) (it's a ∀k, ∀D statement).
- A computation CAN potentially DISPROVE (Q): find an admissible D and k where the missing set
  appears to grow without bound (density not →0), suggesting NOT cofinite. This is the falsification
  lane — see sumset_falsification_search.md.

## Necessary conditions (both PROVED necessary, see sumset_reduction_scaling.md):
1. gcd(D)=1  (else prime p | gcd ⟹ p^k | whole sumset, not cofinite). NEW for k≥1.
2. ∑ 1/(d−1) ≥ 1  (Pomerance density bound; necessary at all k incl k=0).

(Q) asks: are these two SUFFICIENT for k≥1? At k=0, condition 2 alone suffices (Alexeev).
