# troika: §C.3 CORRECTION — the bridge is equidistribution, not power-alignment (death point)

lift flagged a real flaw in my §C.3 / §C.3a. After independent verification I CONCUR: the
triple-power-alignment framing is WRONG. This documents the correction and my tool assessment
(the team-lead's requested "exact death point").

## What was wrong
§C.3 claimed: "B₃+B₄ gaps have total relative measure → 0, so a hole survives only if a base-7 value,
a 3-power, and a 4-power ALIGN." **The premise is false.** Verified independently
(`/tmp/e124_gap_measure.py`): the B₃+B₄ uncovered fraction in dyadic windows is 8–21% (lift measured
19–39% with a different window) — POSITIVE and oscillating, NOT vanishing. So a point can be uncovered
by B₃+B₄ with no power-alignment at all, just by sitting in the positive-measure gap set. The
"hole ⟹ triple alignment" implication does not hold. My §C.3a knife-edge was the wrong mechanism.

## The correct mechanism (verified)
n > 581 is covered because n = (B₃+B₄ value) + (B₇ value) has MANY solutions, with a GROWING margin:
- min number of base-7 representations of n over [1000, 2·10⁶] is **10, and grows**: 10 → 40 → 63
  across scales [1e3,1e5], [1e5,5e5], [5e5,1.5e6] (`/tmp/e124_correlation.py`). Median ~57 → 197.
- Each single base-7 shift c covers ~77% of any given B₃+B₄ gap (= the local covered-complement
  density); the UNION over the ~log₇(n) available shifts closes the gap (`/tmp/e124_equidist.py`).
- The local density of B₃+B₄ dips to 0 inside each gap (gaps are wider than any fixed window), so a
  single shift can miss; covering requires DIFFERENT shifts to hit DIFFERENT sub-regions of the gap.

**So the bridge is a DENSITY-OVERLAP + EQUIDISTRIBUTION statement:** the base-7 lattice {7^l} and its
subset-sums must equidistribute across the internal covered/uncovered pattern of each B₃+B₄ gap, so
that no n in the gap is missed by every shift. This is a CORRELATION/joint-equidistribution
statement, not a pairwise-alignment statement.

## Tool assessment (the team-lead's question: MW or circle method?)
**MW alone does NOT close it.** MW (linear forms in two logs) bounds the PAIRWISE spacing
|3^p − 7^r|, |3^p − 4^q|, etc. — it controls where individual power-coincidences sit. But the bridge
needs the JOINT behavior: that across all ~log₇(n) base-7 shifts, their images mod the gap structure
cover the gap. Pairwise spacing bounds do not directly yield joint equidistribution. The honest
position:
- **The right tool is exponential-sum / circle-method / Weyl-equidistribution** of the sequence
  {l·log7 mod (log3, log4 lattice)} — i.e. that the base-7 ray does not concentrate in the
  B₃+B₄ gap bands. This is the same flavor as Mauduit–Rivat / Maynard digit-distribution work
  (scholar's tool #12), NOT BEGL's MW route.
- **MW's residual role:** it may still be needed to rule out the worst single near-coincidence (the
  k=1 hole 581 does sit at the tightest triple 3^5≈4^4≈7^3), i.e. to handle the finite "bad" scales;
  but the asymptotic closure is equidistribution.

## Consequence for theorem_347_allk.md
- §A, §B (lift, k-uniformity) remain RIGOROUS.
- §C.2 (B₃+B₄ gaps unbounded, ∝ top power) remains correct and is now even more central.
- **§C.3/§C.3a must be retracted/reframed**: the bridge is equidistribution of base-7 across the
  gap structure, with growing covering margin (min reps 10 → 63), not triple-alignment. The effective
  closure needs an exponential-sum bound, which is HARDER than citing MW Cor 10.1.
- **This is the genuine death point**: the theorem does NOT close by MW alone. It reduces to a
  base-7 equidistribution / exponential-sum estimate over the B₃+B₄ gap bands. Whether BEGL96's
  actual (3,4,7) s=1 proof used such an estimate (hidden in their finite computation to 581) or a
  cleverer elementary covering is the next thing to check against the paper. For all-k, the
  equidistribution must be uniform — that is the real open analytic content.

## Honest status
The "complete-modulo-one-MW-constant" claim I made earlier is WITHDRAWN. The correct status:
the theorem reduces (via §A,§B,§C.2 + the growing-margin covering) to a base-7 equidistribution
estimate; that estimate is the open core and is circle-method territory, not a single MW constant.
This is less finished than I claimed but is the TRUTH, and pins the exact analytic obstruction.
