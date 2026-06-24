# Density's contributions to the E124 conclusion document (task #21)

**Author:** density (measure/mass lens). Conclusion-ready summary of the measure-side findings, with
honest scope labels. For the unified conclusion document. All cross-validated; all overclaims (caught
by maverick/cassels/sumset adjudication) already withdrawn.

## ELEMENTARY, PROVED (writeup-ready, no caveats)

1. **Astels thickness identity.** The Newhouse thickness of B_d is τ(B_d) = 1/(d−2), so the Astels
   normalized thickness γ(B_d) = τ/(1+τ) = **1/(d−1) exactly**. Therefore the BEGL96 admissibility
   threshold ∑1/(d−1) ≥ 1 IS Astels' sum-of-normalized-thicknesses condition ∑γ(B_d) ≥ 1. A
   structural explanation of WHY the threshold has its form (additive, =1, sharp). [NEW framing.]

2. **S9 forward lemma (top-of-power gaps).** ∑1/(d−1) ≥ 1 ⟹ NO top-of-power gap, for all admissible
   D. Proof: maxB(d,X) = (d^{L+1}−1)/(d−1) with d^{L+1} > X ⟹ maxB(d,X) ≥ X/(d−1); summing,
   ∑_d maxB(d, d_min^m−1) ≥ (d_min^m−1)·∑1/(d−1) ≥ d_min^m−1, so the gap inequality fails. ∎
   Independently verified (scholar): zero violators across all 45 admissible D, d∈3..12, r≤4.

3. **Constructive Pomerance converse.** ∑1/(d−1) < 1 ⟹ not cofinite, via Weyl equidistribution
   producing a missing block just below d_min^m for infinitely many m. Concrete: (3,6,7), n=40,342,197
   unreachable by exactly 1 (brute-force verified). Edge case (mult-dependent bases) excluded by gcd=1.

4. **No-prime-power-collinear lemma.** No admissible D is a set of powers of one prime: T_p =
   ∑_{j≥1} 1/(p^j−1) ≤ T_3 = 0.682 < 1 (odd p); p=2 towers force gcd > 1. ⟹ admissible D carries
   ≥ 0.318 harmonic mass off any single prime tower (forced multiplicative spread). Settles scholar's
   sharp test; the structural antidote to Melfi's zero-density pathology.

## TWO-EXPONENT PICTURE (joint with lift, PROVED-elementary)

Two distinct supercritical exponents: **reach surplus** δ = ∑1/(d−1) − 1 (governs cofiniteness via
the MIN representation count) and **counting surplus** ε = ∑(log2/log d) − 1 (governs the AVERAGE
count, r_D(n) ~ n^ε). **ε > δ strictly** (⟺ 2^{d−1} > d term-by-term). At the boundary (3,4,7):
δ = 0 but ε = 0.487 > 0. So the average count diverges even where cofiniteness is critical — the
cleanest articulation of WHY BEGL96 is hard exactly at β=1: cofiniteness needs the MIN ≥ 1 (controlled
by δ=0 reach, MW), while the AVERAGE is free (ε > 0). [note_two_exponents.md]

## THE OPEN CORE, PRECISELY LOCALIZED (the campaign's sharpest handle)

**Run-vs-singleton decomposition.** Cofiniteness = (no missing RUN of length ≥2 above the run-bound)
+ (no isolated SINGLETON above N₀). Verified ({3,4,6} k=2): last run≥2 at 44,817, last singleton =
N₀ = 242,113 (5.4× higher). The two halves:
- **RUN-BOUND (elementary, Baker-conditional, DERIVED):** runs come from the two-largest-scale
  Frobenius gap, size ≤ |d_max^a − d_2^b| ≥ c·U^{1−κ} by Baker (SUBLINEAR); the surplus σ·U is LINEAR;
  so σ·U dominates above X_run = (C/σ)^{1/κ} ⟹ no run ≥2 above X_run. Validated: octave max-run-length
  → 0 with scale. This is density+carry's elementary leg.
- **SINGLETON RESIDUAL (the MW core):** isolated run-length-1 misses persisting to N₀ — single
  non-representable values whose locations are cross-base power-coincidences (|d_max^a − d_2^b| small).
  maverick's unification: these singletons are the SAME object across ALL dead routes (Φ=0
  large-deviations, sumset's non-automaticity points, troika's 2-torus fat-boundary). The irreducible
  transcendence.

**This is the cleanest concrete statement of the elementary/MW boundary the team produced.**

## CONDITIONAL / HONEST-RESIDUE PARTIALS

- **Triangulated joint lemma (with cassels):** per-fixed-k cofiniteness, hyp = gcd(D)=1 + σ>0 ONLY
  (gcd-top-two NOT needed — vestigial, dropped). N₀ = v + d_min^k, v ~ gap(D,k)/σ. Surplus (density
  front) + Lemma C (cassels back), transcendence-free GIVEN gap = O(d_max^k). The O-constant is
  k-DEPENDENT (grows for tight D: {3,4,5} 3.95→194→541); uniform-in-k boundedness = residual MW. Three
  names one threshold: cassels' v = density's U₀ = sumset's last-hole.
- **High-margin theorem (with maverick, in progress):** δ > δ₀(D) [δ₀ = combined multi-pair clustering
  g*, transcendental] ⟹ per-fixed-k effective cofiniteness. gcd(d_max,d_2nd)=1 is the Baker-clean
  CORNER (Baker bounds the top-two clustering ⟹ any δ>0 works there) — SUFFICIENT not necessary
  ({3,4,9,12} gcd=3 still bounded). Baker-conditional, per-fixed-k (NOT k-uniform — {3,4,5} refutes).

## WITHDRAWN (do not include — overclaims caught in adjudication)
- "k-uniform geometric bound N₀ ≤ C·(d_max·d₂)^k with C k-independent" — REFUTED by {3,4,5}.
- "transcendence-free strict-excess theorem" — MISLABEL; it's BAKER-CONDITIONAL.
- gcd(d_max,d_2nd)=1 as a hypothesis of cofiniteness — VESTIGIAL; only governs the withdrawn bound.

## ANALYTIC FRONTIER (live, handed to harmonic-analysis team)
INV-S10 (= my INV-D4 reframe): the Riesz-product minor-arc bound |F_3·F_4·F_7| ≪ N^{3−δ} is the
analytic face of the singleton/MW core; if proved it closes (3,4,7)-all-k. Measure-side evidence:
favorable (scholar's integral decays ~2× faster than sup; breaker's decorrelation rate c∈[0.17,0.31]
k-uniform; my exponent accounting 1.528 < 1.585 conservative). The rigorous sharp ∏|cos| bound via
continued-fraction/Ostrowski geometry is scholar/troika/lift's open step.

## ONE-LINE SUMMARY FOR THE CONCLUSION
The conjecture is almost certainly TRUE. The measure side proves the threshold IS the Astels thickness
condition, kills the coarse (top-of-power/run) gaps elementarily (S9 lemma + Baker-conditional
run-bound), and localizes the entire open content to isolated single-value misses (run-length-1) whose
positions are cross-base power-coincidences = Mignotte–Waldschmidt. The analytic route to those
(INV-S10 Riesz decorrelation) is numerically favorable and k-uniform; the rigorous bound is the one
remaining piece.
