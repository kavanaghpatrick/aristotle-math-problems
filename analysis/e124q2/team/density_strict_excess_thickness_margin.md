# Strict-excess: the thickness-margin closes sumset's "step 2" (no transcendence)

**Author:** density, building on sumset_strict_excess_lead.md (the MAIN LINE) and my
density_thickness_assault.md. **Status:** mechanism identified + computationally supported.
This is the measure-side ingredient for an elementary uniform-in-k theorem on strict-excess E124.

> **CORRECTION (maverick's immune-system catch, verified).** The clean geometric bound
> threshold ≤ C(δ)·(d_max·d_2)^k is FALSE as originally stated: it requires the extra hypothesis
> **gcd(d_max, d_2nd) = 1** (two largest bases coprime). Counterexample {3,4,6} (δ=+0.033, gcd=1,
> admissible): top two are 4,6 with gcd 2, so 6^a vs 4^b = |2^a·3^a − 2^{2b}| carries a shared-prime
> |2^·−·| MW pair at the BINDING scale ⟹ C = thr/24^k GROWS ~10×/k (41 → 420 → 4264 for k=1,2,3),
> and n₀(1)=986 > the boundary (3,4,7)'s 581. I sharpened maverick's "fully multiplicatively
> independent" to the WEAKER, exact condition **gcd(d_max, d_2nd)=1**: only the two largest bases
> (the binding scale, per sumset's Frobenius anatomy) must be coprime; shared primes among smaller
> bases are harmless. Verified: (3,4,5,6,7) [top two 6,7 coprime], (4,5,6,7,8) [7,8], (3,4,6,7)
> [6,7], (3,4,5,9) [5,9], (3,4,5,8) [5,8] ALL have bounded C despite shared primes among smaller
> bases. The theorem below should carry the hypothesis gcd(d_max,d_2nd)=1. See §"Corrected hypothesis".

## The setup (sumset's dichotomy, confirmed)
- **Boundary ∑1/(d−1) = 1** (e.g. (3,4,7)): threshold driven by Mignotte–Waldschmidt (transcendence).
  Verified signature: at k=3, max gap in the upper half is still >1 at N=10^8 (threshold 166M sits
  above N/2), i.e. the last holes are pushed up to the MW scale.
- **Strict excess ∑1/(d−1) = 1+δ, δ>0** (e.g. (3,4,5,7), δ=0.25): threshold ≤ C(D)·(d_max·d_2nd)^k,
  geometric. Verified: max gap in upper half = 1 already at modest N (threshold ≪ scale).

## The thickness-margin mechanism (why strict excess is elementary)

In the Astels/thickness picture, ∑γ(B_d) = ∑1/(d−1) = 1+δ. At the boundary (δ=0), the discrete
superadditivity failure (density_thickness_assault.md DP4 — the power-aligned top-of-power gap of a
partial sumset is exactly as large as the remaining mass can cover, no slack) forces MW to control
the alignment. **With margin δ>0, the remaining mass OVER-covers the power-aligned gap by a factor
tied to δ**, so the gap is bridged without needing the alignment controlled — elementary.

Quantitatively: the binding gap near scale x is a top-of-power gap of size ≈ x·(fraction). The
margin supplies extra reach ≈ δ·x. The last hole (threshold) is where the cumulative margin reach
first dominates the largest single-base power-gap — a GEOMETRIC condition in the two largest scales,
giving threshold ≤ C(D)·(d_max·d_2nd)^k. This is precisely sumset's empirical law and the
"two-largest-scale Frobenius gap" anatomy (no linear-forms-in-logs).

## Computational support: the constant collapses with margin

k=3 strict-excess thresholds (sumset's exact-bitset data), C := threshold/(d_max·d_2nd)^3:

| D | ∑1/(d−1) | δ | threshold | (d_max·d_2)^3 | C | C·δ |
|---|---|---|---|---|---|---|
| (3,4,5,7) | 1.250 | 0.250 | 78,426 | 42,875 | 1.829 | 0.457 |
| (3,4,5,6,7) | 1.450 | 0.450 | 11,574 | 74,088 | 0.156 | 0.070 |
| (3,4,5,6,7,9) | 1.575 | 0.575 | 6,253 | 250,047 | 0.025 | 0.014 |

**C decreases steeply as δ grows** (1.83 → 0.16 → 0.025) — even faster than 1/δ. So the threshold
constant is controlled by the margin: larger harmonic surplus ⟹ smaller threshold constant ⟹ the
geometric bound bites sooner. This is the quantitative face of "the margin gives the slack to turn
bounded-gap into gap=1" (sumset's open step 2).

## The combined target (density × sumset)

> **(Strict-excess BEGL, all k).** D admissible, gcd(D)=1, ∑1/(d−1) = 1+δ with δ>0. Then T_k(D) is
> cofinite for every k≥1, with threshold ≤ C(δ,D)·(d_max·d_2nd)^k, C decreasing in δ.

Proof obligation, now split cleanly:
1. **Residue half** — DONE (sumset Theorem B + scale-route: gcd=1 ⟹ all residues mod every M, no
   transcendence).
2. **Bulk/gap half** — the thickness-margin mechanism above. The remaining rigorous step: prove the
   margin δ over-covers the largest power-aligned partial-sumset gap at scale x, uniformly, so the
   last hole is at most C(δ)·(d_max·d_2)^k. The Astels gap-condition with slack δ should give this
   WITHOUT MW (unlike the boundary, where δ=0 leaves no slack and MW is forced).

## Honest scope
This does NOT prove the boundary case ∑=1 (the conjecture's literal hypothesis includes ∑≥1, so the
boundary (3,4,7)-type families are IN scope and remain MW-only). But a clean strict-excess theorem
would be a genuine partial advance: BEGL96 only displayed the single boundary family (3,4,7); no
general strict-excess result is in the literature. The thickness-margin gives the right elementary
mechanism; the open obligation is making step 2 rigorous and uniform. Recommend density+sumset
co-develop step 2.

## Corrected hypothesis (the precise condition, verified)

> **(Strict-excess BEGL, corrected).** D admissible, gcd(D)=1, ∑1/(d−1)=1+δ>1, **AND
> gcd(d_max, d_2nd)=1**. Then T_k(D) is cofinite ∀k≥1, threshold ≤ C(δ,D)·(d_max·d_2nd)^k.

Why exactly the two largest: sumset's last-hole anatomy localizes the binding obstruction to the
two-largest-scale Frobenius gap |d_max^a − d_2nd^b|. If gcd(d_max,d_2nd)=g>1, that difference shares
a prime, becoming a |p^·−·| Mignotte–Waldschmidt near-coincidence at the binding scale — clustering
the holes and breaking the geometric bound. If gcd(d_max,d_2nd)=1 the two top bases are
multiplicatively independent, the |d_max^a−d_2^b| spacing is MW-clean (bounded below polynomially),
and C stays bounded.

EXACT-computation evidence (C := threshold/(d_max·d_2nd)^k):

| D | δ | gcd(d_max,d_2) | C(k=1) | C(k=2) | C(k=3) | verdict |
|---|---|---|---|---|---|---|
| {3,4,6} | 0.033 | gcd(4,6)=2 | 41 | 420 | 4264 | **PATHOLOGY** (C grows ~10×/k) |
| {3,4,5,7} | 0.250 | gcd(5,7)=1 | 0.63 | 0.57 | 1.83 | bounded ✓ |
| {3,4,5,6,7} | 0.450 | gcd(6,7)=1 | 0.05 | 0.18 | 0.16 | bounded ✓ |
| {4,5,6,7,8} | 0.093 | gcd(7,8)=1 | 0.05 | 0.76 | 0.49 | bounded ✓ |
| {3,4,6,7} | 0.200 | gcd(6,7)=1 | 0.57 | 1.17 | 2.51 | bounded ✓ |
| {3,4,5,9} | 0.208 | gcd(5,9)=1 | 0.33 | 1.60 | 1.58 | bounded ✓ |
| {3,4,5,8} | 0.012 | gcd(5,8)=1 | 0.25 | 0.76 | 0.92 | bounded ✓ |

The condition gcd(d_max,d_2nd)=1 is STRICTLY WEAKER than full pairwise-coprimality / multiplicative
independence (maverick's first cut): {3,4,5,6,7}, {4,5,6,7,8}, {3,4,6,7} all have shared primes
among the SMALLER bases yet are well-behaved — only the top two matter.

## Impact on the margin leg
My margin-growth mechanism (surplus δ·U overtakes the residual gap) is UNAFFECTED in its surplus
half — the surplus δ·U is correct regardless. What {3,4,6} shows is that the RESIDUAL alignment gap
is NOT O(d_max^k) when gcd(d_max,d_2nd)>1 — it is MW-clustered and larger. So the shared obligation
(sumset+carry: residual gap = O(d_max^k)) HOLDS only under gcd(d_max,d_2nd)=1. The corrected
flagship theorem carries that hypothesis; {3,4,6}-type families fall back to the MW boundary regime
even though they have strict excess. This is a real refinement of the theorem's scope.

## HONESTY CORRECTION to the corrected hypothesis (don't overclaim)

Further testing shows gcd(d_max,d_2nd)=1 is SUFFICIENT for bounded C but NOT NECESSARY:
- {3,4,9,12}: gcd(9,12)=3 > 1 (top two NOT coprime), yet C DECREASES 8.1 → 5.5 → 4.2 (k=1,2,3,
  thresholds 879 / 63,989 / 5,233,049, verified stable at N=5×10^8) — BOUNDED, no pathology.
- {3,4,6}: gcd(4,6)=2, C DIVERGES 41 → 420 → 4264 (threshold 58,941,162 at k=3 stable to N=8×10^8).

So gcd(d_max,d_2nd)>1 does NOT always cause the pathology. The SAFE theorem hypothesis is
**gcd(d_max,d_2nd)=1 ⟹ bounded C** (sufficient; all 6 coprime-top-two test families bounded). The
EXACT necessary condition for the {3,4,6} pathology is narrower and not yet pinned — {3,4,6} (r=3,
δ=0.033, every base pairwise-entangled: 6 shares 2 with 4 and 3 with 3) is more degenerate than
{3,4,9,12} (r=4, more surplus mass). Likely the pathology needs BOTH gcd(d_max,d_2nd)>1 AND low
redundancy (small r / small δ relative to the clustering). 

**Net honest statement:** the strict-excess theorem is provably FALSE without SOME extra hypothesis
({3,4,6} kills the unconditional version, maverick's catch confirmed). gcd(d_max,d_2nd)=1 is a clean
SUFFICIENT extra hypothesis that rescues it. Whether a weaker condition suffices is open; do not
claim the theorem for all gcd(d_max,d_2nd)>1 families (some, like {3,4,9,12}, are fine).

## UNIFICATION with maverick's competition framing (the correct final statement)

maverick refined: it's not "exclude MW pairs" (every admissible D has them — ≥2 primes) but a
COMPETITION between the margin δ and the worst cross-base clustering, effective iff δ > δ₀(D).
This UNIFIES with my gcd(top-two)=1 condition:

- **δ₀(D) is set by the closest relative approach c(D) := min |d_max^a − d_2nd^b| / scale** of the
  two largest bases (the binding scale). Measured (closest approach over powers < 10^18):
  | family | gcd(top-two) | closest approach c | δ | δ/c | outcome |
  |---|---|---|---|---|---|
  | {3,4,6} | 2 | 0.038 | 0.033 | 0.9 | DIVERGES |
  | {3,4,9,12} | 3 | 0.076 | 0.049 | 0.6 | bounded-but-elevated (C~5) |
  | {3,4,5,7} | 1 | 0.044 | 0.25 | 5.7 | clean |
  | {3,4,5,6,7} | 1 | 0.056 | 0.45 | 8.0 | clean |
  | {3,4,6,7} | 1 | 0.056 | 0.20 | 3.5 | clean |
  | {3,4,5} | 1 | 0.033 | 0.083 | 2.5 | clean |

- **Why gcd(top-two)=1 is the clean sufficient proxy:** when the two largest bases are coprime,
  Baker's theorem bounds |d_max^a − d_2nd^b| below polynomially, so c(D) cannot be made arbitrarily
  small by alignment — δ₀(D) stays small and essentially ANY δ>0 clears it (all coprime-top-two
  families above have δ/c ≥ 2.5, clean). When gcd(top-two)>1, powers can ALIGN closely (small c),
  pushing δ₀ up; then only LARGE δ wins ({3,4,6}'s δ=0.033 loses, would need much more margin).

- **The honest hierarchy of statements:**
  1. SHARP (maverick): effective iff δ > δ₀(D), δ₀ set by the cross-base clustering c(D). δ₀ is
     itself an MW quantity (closest approach of powers), so the sharp threshold is transcendental.
  2. CLEAN SUFFICIENT (density): gcd(d_max, d_2nd)=1 ⟹ δ₀(D) small (Baker floor) ⟹ any δ>0 in the
     strict-excess theorem works. This is a transcendence-FREE hypothesis that isolates a large
     effective sub-class.
  3. The theorem is best stated as a HIGH-MARGIN result: "∑1/(d−1) ≥ 1+δ with δ > δ₀(D)" OR the
     clean "gcd(d_max,d_2nd)=1 + strict excess" — both genuine, both with caveats above.

**Net:** maverick's catch + my sharpening + this unification give a HONEST partial theorem:
the strict-excess result holds for the coprime-top-two sub-class (transcendence-free, any δ>0),
and more generally above a D-dependent margin δ₀ that is itself MW. Not "all strict excess," but a
large, cleanly-described effective sub-class — a real partial advance on E124-open (BEGL96 gave
only the single boundary family (3,4,7)).

## ADJUDICATION EXTENSION (maverick) — TWO CORRECTIONS, both accepted

**CORRECTION 1 — the geometric bound is REFUTED.** My "threshold ≤ C(δ,D)·(d_max·d_2nd)^k with C
k-independent" is FALSE. Counterexample {3,4,5} — which satisfies ALL my hypotheses (gcd(D)=1,
∑=13/12>1, gcd(5,4)=1): N0/20^k = 3.95 → 194 → 541 (k=1,2,3), GROWS with k. Verified (true N0 =
79/77613/4330731). So C is NOT k-independent and the (d_max·d_2nd)^k scale is the WRONG ansatz —
N0 grows faster (log_20 N0 increments 2.3, 1.3 — super-linear early). The bound held for (3,4,5,7)
(C=0.63/0.57/1.83, bounded) but that was luck of that family, not a theorem. **gcd(top-two)=1 is
NECESSARY (correctly kills the {3,4,6} corner) but NOT SUFFICIENT for any clean geometric bound.**

**CORRECTION 2 — "transcendence-free" is a MISLABEL.** My proof of the gcd(top-two)=1 corner invokes
a "Baker floor" (Baker's lower bound on |d_max^a − d_2nd^b|) to bound the clustering c(D). Baker's
theorem IS transcendence. So the honest label is **BAKER-CONDITIONAL**, not transcendence-free. The
elementary/transcendence-free claim was wrong wherever the Baker floor is used.

### What actually survives (the real, correctly-labeled contributions)
1. **gcd(d_max, d_2nd)=1 is the necessary corner-killer** (vindicated by {3,4,6}; verified necessary).
2. **The margin-vs-clustering picture** (δ vs g*(D)) — qualitatively correct framing.
3. **The thickness-margin mechanism** (γ(B_d)=1/(d−1) = Astels; surplus δ·U bounds RUNS).
4. **The RUN-BOUND** (no missing run of length ≥2 above some scale) — this does NOT depend on the
   refuted (d_max·d_2)^k ansatz; it only needs the surplus to exceed the run-length, which holds.
   But it is BAKER-CONDITIONAL (the g* bound uses Baker) and is NOT cofiniteness (singletons remain).

### Correctly-labeled final statement (no overclaim)
> Within the canonical split (non-minimal D = elementary via Lemma M; minimal D = open MW/Baker),
> gcd(d_max,d_2nd)=1 refines WHICH minimal families are hardest (the shared-prime-top-two ones, like
> {3,4,6}, are the worst), but does NOT make any minimal family elementary. There is NO clean
> geometric threshold bound; the best correctly-labeled result is the BAKER-CONDITIONAL run-bound.

This supersedes the "transcendence-free geometric strict-excess theorem" claimed earlier in this
file and in density_margin_growth_leg.md — those statements are WITHDRAWN as overclaims. The
genuine, defensible contributions are items 1–4 above, correctly labeled.

## HIGH-MARGIN THEOREM (co-authoring with maverick) — two compatible statements + a C-growth flag

The high-margin theorem (maverick's δ>δ₀ framing + my Baker corner) is a DIFFERENT, compatible
object from the cassels joint lemma:
- **Joint lemma (cassels+density):** per-fixed-k cofiniteness, hyp = gcd(D)=1 + σ>0 ONLY (no gcd-top-two).
  Covers ALL admissible D; {3,4,6} included (N₀ finite each k). [statement (A)]
- **High-margin theorem (maverick+density):** effective cofiniteness for the sub-class δ > δ₀(D),
  δ₀ ≍ c(D) (closest top-two power approach, MW). {3,4,6} OUT (δ/c=0.85<1); {3,4,5,7} IN (δ/c=5.46).
  [statement (B) RESTRICTED to its domain — NOT the refuted unconditional (B)]
Structure: MAIN (sharp, δ>δ₀, δ₀ is MW/transcendental); CLEAN COROLLARY (gcd-top2=1 ⟹ Baker floor on
c(D) ⟹ δ₀ small ⟹ any δ>0 in the corner); CAVEAT (sufficient not necessary, e.g. {3,4,9,12} gcd=3
bounded). Baker-conditional at the foundation, transcendence-free in the combinatorics above.

**C-GROWTH FLAG (load-bearing, flagged to maverick before locking MAIN).** With only k≤3 data, the
threshold constant C = N₀/(d_max·d₂)^k GROWS at k=2→3 even for moderately-high δ/c:
| family | δ/c | C(k=1,2,3) | k2→k3 |
|---|---|---|---|
| {3,4,5} | 2.45 | 3.95 / 194 / 541 | 2.8× (grows) |
| {3,4,5,7} | 5.46 | 0.63 / 0.57 / 1.83 | 3.2× (grows!) |
| {3,4,6,7} | 3.35 | 0.57 / 1.17 / 2.51 | 2.1× (grows) |
| {3,4,5,6,7} | 7.53 | 0.05 / 0.18 / 0.16 | 0.9× (flattens) |
Only the VERY highest δ/c flattens. So "δ>δ₀ ⟹ k-UNIFORMLY bounded C" is NOT established by k≤3 and
is exactly what {3,4,5} refuted. **The defensible MAIN is PER-FIXED-K** (C grows slower for higher
δ/c, flattening only as δ/c→large), NOT k-uniform bounded-C. Awaiting maverick's confirmation /
k=4,5 high-δ/c data before locking the MAIN wording.
