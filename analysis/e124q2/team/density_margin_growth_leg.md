# Strict-excess flagship: the measure/margin leg — the covering margin GROWS with scale

**Author:** density. **Status:** mechanism identified + EXACT-computation verified; central
inequality stated, reduction to sumset/cassels' threshold complete. My leg of the four-angle
strict-excess theorem (∑1/(d−1) ≥ 1+δ ⟹ cofinite ∀k). Coordinates with lift (boundary margin
measurement), sumset+carry (two-phase invariant), cassels (effective thr_r).

## The task (from lift's measurement)
lift measured the covering margin at the BOUNDARY ∑=1 to be **thin and STATIC** (1.5×–3×, not
growing — `lift_bridge_quantified.md`): at the 3^15 gap of B_3+B_4, base-7 shifts needed ≈ 293,
available 512, margin 1.75× (I independently reproduced 1.75×). The criticality signature of ∑=1.
**My leg: prove that with strict excess δ>0 the margin GROWS with scale** — that is what separates
the elementary regime from the MW boundary.

## The correct margin object (general — works for ALL strict excess)

A first attempt — "drop the largest base d_r, cover its sub-sumset's gaps with B_{d_r}" — gives a
growing margin ONLY when ∑_{d≠d_r} 1/(d−1) ≥ 1 (sub-family already admissible). That FAILS for
e.g. (3,4,5) (δ=0.083, drop any → sub-∑ < 1) and (4,5,6,7,8) (δ=0.093, drop 8 → 0.95 < 1). Too
crude.

The RIGHT object is the **total surplus reach**. At scale U, the combined max-reach mass of all
bases is (∑1/(d−1))·U·(1+o(1)) = (1+δ)·U·(1+o(1)). The bulk needs U to cover [0,U]; the **surplus
is δ·U**, growing LINEARLY in U. The residual to absorb is the alignment gap (the two-largest-scale
Frobenius gap, sumset's last-hole anatomy), which is BOUNDED in U for fixed k. Hence

    margin(U) = (surplus reach δ·U) / (residual alignment gap)  ~  δ·U / (C·d_max^k)  →  ∞.

**The margin grows linearly in U for every δ > 0** — independent of whether any single base is
droppable. This is the measure-side statement.

## EXACT-computation verification (the load-bearing check)

Largest gap of the FULL sumset T_k in the upper half [N/2, N] (C bitset, exact):

| family | δ | k | N=10^6 | N=5×10^7 | verdict |
|---|---|---|---|---|---|
| (3,4,5,7) | 0.25 | 1 | 1 | 1 | bounded, U-independent |
| (3,4,5) | 0.083 | 1 | 1 | 1 | bounded (small δ!) |
| (4,5,6,7,8) | 0.093 | 1 | 1 | 1 | bounded (no base droppable!) |
| (3,4,5) | 0.083 | 2 | 1 | 1 | bounded at k=2 |

For EVERY strict-excess family — including the two that defeated the "drop a base" theory — the
largest gap above the threshold is exactly **1** and does NOT grow with U. The surplus δ·U overtakes
the alignment gap at a finite threshold, after which the gap is 1 forever. This is precisely
"margin → ∞", confirmed exactly. Contrast: boundary (3,4,7) at k=3 still has gap > 1 at N=10^8
(threshold 166M, MW-driven).

## The central inequality (the rigorous obligation)

> **(MARGIN-GROWTH).** D admissible, gcd=1, ∑1/(d−1) = 1+δ, δ>0. There is X₀(δ,D,k) such that for
> all U ≥ X₀, the surplus reach available to cover the largest residual gap ending at U strictly
> exceeds that gap. Quantitatively X₀ ≤ C(δ,D)·(d_max·d_2nd)^k, so for U ≥ X₀ the sumset has no gap.

This is EXACTLY the finiteness of sumset/cassels' threshold thr_r. My leg supplies the MECHANISM
(surplus δ·U vs bounded alignment gap) and the reduction; the QUANTITATIVE bound X₀ ≤ C(δ)·(d_max·d_2)^k
is cassels' effective-threshold leg / sumset's two-phase invariant. The pieces compose:
- **surplus grows linearly** (δ·U) — my max-reach ledger (γ(B_d)=1/(d−1), worst-case reach exact).
- **alignment gap bounded by C·d_max^k** — sumset's last-hole anatomy (two-largest-scale Frobenius).
- **surplus overtakes gap at U₀ = (alignment gap)/δ ~ C·d_max^k/δ** — hence the 1/δ dependence in
  the threshold constant I measured earlier (C·δ ≈ const: 0.46, 0.07, 0.014 — the threshold
  constant scales like 1/δ as this predicts, modulo the geometric (d_max·d_2)^k factor).

## Surplus lower bound — RIGOROUS and verified (the part I own)

The surplus reach is ≥ δ·U as a guaranteed floor, with room to spare. Max reach of B_d in [0,U] is
∑_{d^j ≤ U} d^j ∈ [U/(d−1), dU/(d−1)), with the minimum U/(d−1) attained when U is just above a
power of d. So worst-case total reach = U·∑1/(d−1)·(1+o(1)) = (1+δ)·U·(1+o(1)), giving surplus
≥ δ·U·(1−o(1)) ALWAYS (the simultaneous-worst-alignment case is the binding floor).

Verified (min over 5×10^5 random U ∈ [10^5,10^9] of total-reach/U):
| family | δ | worst total-reach/U | surplus/U floor |
|---|---|---|---|
| (3,4,5) | 0.083 | 1.244 | ≥ 0.244 |
| (3,4,5,7) | 0.250 | 1.557 | ≥ 0.557 |
| (4,5,6,7,8) | 0.093 | 1.581 | ≥ 0.581 |

The measured surplus floor EXCEEDS δ — the bases rarely hit worst alignment simultaneously, so the
guaranteed surplus is δ·U but typically much larger. **The surplus is NOT the binding constraint**;
it is amply available and grows linearly. The binding constraint is purely whether the gaps ALIGN,
which is the alignment-gap bound (sumset+carry's leg). My leg certifies the surplus side is solid.

## What is rigorous vs open (honest)
- RIGOROUS: surplus reach ≥ δ·U·(1−o(1)), o(1) uniform, verified above (floor exceeds δ with margin).
  The residual gap is ≤ the largest top-of-power gap of the sub-sumset, bounded by the
  two-largest-scale span.
- OPEN obligation (shared with sumset/cassels): prove the residual alignment gap is genuinely
  O(d_max^k) and not secretly U-growing — i.e. that the "bulk" reach (1·U) covers everything except
  a span localized to the two largest scales. This is the carry/two-phase-invariant lemma
  (sumset+carry's leg). My contribution certifies that ONCE that holds, the surplus δ·U closes it
  with margin → ∞, uniformly in k (the surplus is scale-invariant in k since ∑1/(d−1) is).

**Net: my leg is DONE as a mechanism + reduction. The margin provably grows (δ·U, verified exact).
The remaining shared obligation is bounding the alignment gap by O(d_max^k), which composes with my
surplus to give the threshold X₀ ≤ C(δ)(d_max·d_2)^k.**

## TRIANGULATION (verified exact): three legs measure ONE threshold

cassels' +M-closure onset T = v+M (Lemma C identity), sumset's last-hole, and my U₀
(surplus-overtakes-alignment) are the SAME number. Verified exact (C bitset):

| family | k | M=b^k | last hole | last +M-fail v | T=v+M | matches sumset anatomy |
|---|---|---|---|---|---|---|
| (3,4,5,7) | 2 | 9 | 695 | 686 | 695 | ✓ |
| (3,4,5,6,7) | 2 | 9 | 312 | 303 | 312 | ✓ |
| (3,4,5,7) | 3 | 27 | 78,426 | 78,399 | 78,426 | ✓ (=42 below 7^3+5^7) |

So: cassels' +M-onset = sumset's geometric threshold C·(d_max·d_2)^k = my U₀ ~ (alignment gap)/δ.
The strict-excess theorem's three quantitative legs are one object, triangulated three ways. The
remaining shared obligation (sumset+carry: alignment gap = O(d_max^k), not U-growing) closes all
three simultaneously, with my surplus δ·U providing the MW-free forcing at strict excess.

## THE RECURRENCE CRITERION δ > g*(D) (derived from Astels gap-condition with slack)

Co-developed with sumset (recurrence observation) and maverick (competition framing). The single
inequality that governs whether gaps recur:

**Surplus vs gap, scale by scale.** At scale X: total max-reach ≥ (1+δ)·X (RIGOROUS, my reach
floor — every base contributes ≥ X/(d−1), summing to (1+δ)X even at simultaneous worst alignment).
The largest residual sub-sumset gap at scale X is ≤ g*(D)·X, where g*(D) is the limsup relative gap
of the binding sub-sumset (= maverick's clustering c(D)). The full-sumset gap survives iff the gap
exceeds the surplus:

> **gaps recur ⟺ g*(D)·X > δ·X ⟺ δ < g*(D)** (scale-invariant).

- **δ > g*(D):** surplus δX beats the gap g*X at EVERY scale ⟹ X* finite ⟹ gaps confined to a
  bounded low range (sumset's empirical observation) ⟹ elementary, uniform-in-k.
- **δ < g*(D):** the gap wins at recurring (equidistributed) scales ⟹ gaps persist to the MW scale
  ⟹ boundary-like, transcendence-required.

This single criterion unifies all three legs: my surplus δX, maverick's competition, sumset's
recurrence cutoff. **The X* bound sumset asked for: X* ≤ C(D)·(d_max·d_2nd)^k / (δ − g*), finite iff
δ > g*(D).**

### Rigor demarcation (honest)
- RIGOROUS: reach floor (1+δ)X; the scale-invariant criterion δ vs g*.
- MW in general: g*(D) is the limsup relative gap, a transcendental quantity (how close
  |d_max^a − d_2nd^b| get). Finite-scale measurements UNDERESTIMATE it.
- **TRANSCENDENCE-FREE CORNER:** gcd(d_max, d_2nd)=1 ⟹ Baker bounds |d_max^a − d_2nd^b| below
  polynomially ⟹ g*(D) ≤ effective Baker constant (small) ⟹ any δ>0 exceeds it ⟹ X* finite,
  elementary. This is the provable step 2 and the scope of the clean theorem.

## CLEAN NEGATIVE (with sumset): reach-based criteria are blind to internal gaps

sumset's decisive counterexample, independently confirmed: **(5,6,7,8,9,10)** has
∑1/(d−1) = 2509/2520 = 0.9956 < 1 (so NOT cofinite, by Pomerance), YET its reach/n stays ≥ ~1.8–2.06
across all scales and its top-of-power margin is positive out to 5^39. So the "reach/n ≥ 2 ⟹
cofinite" (double-coverage) criterion is FALSE, and the top-of-power/max-reach/thickness analysis is
BLIND to this family's non-cofiniteness.

**Why my margin leg survives this as a SCOPED result.** My margin-growth leg correctly handles the
TOP-OF-POWER (coarse) gaps — which are the easy gaps, covered for all admissible D including the
boundary. What it does NOT see are the INTERNAL gaps (between powers), which carry the MW-hard
content and are invisible to any reach/coverage measure. So:
- The δ·U surplus dominates the COARSE (top-of-power) obstruction — rigorous, my leg.
- It does NOT dominate the INTERNAL gaps — those need MW (the residual-gap=O(d_max^k) assumption is
  exactly the unproven internal-gap bound, which fails for reach-blind families like (5,6,7,8,9,10)).

**This is the 4th independent angle** (residue [done], bulk/value-coverage [sumset], +M-closure
[cassels], thickness/reach [density]) ALL hitting the same internal-gap/MW wall. The measure-side
contribution is now fully scoped: the top-of-power formula PREDICTS where coarse gaps sit (validated,
e.g. (4,5,6)→241025) but CANNOT prove cofiniteness — the internal gaps are the open MW core.

**Residual value of the margin leg (honest):** (1) the surplus δ·U bound is rigorous and explains
the geometric threshold law for the coarse part; (2) the gcd(d_max,d_2nd)=1 + strict-excess theorem
stands AS A CONDITIONAL result — but its proof still requires the internal-gap residual to be
O(d_max^k), which is itself the MW-hard piece, so the "transcendence-free" claim holds only modulo
that bound (which Baker supplies for coprime-top-two). Net: the measure side cleanly delimits coarse
(solved) vs internal (MW) and quantifies the coarse part; it does not close the conjecture.

## SHARPENED DEATH POINT (sumset): margin kills RUNS, not isolated SINGLETONS

sumset pinned the exact gap in the composition, independently verified by me:

The surplus δ·U is a LENGTH argument — it bounds the longest missing RUN (consecutive gap). Verified
(C bitset, k=2): the last missing run of length ≥2 dies at ~C·d_max^k and shrinks with U:
| family | k | last run≥2 | last SINGLETON | d_max^k |
|---|---|---|---|---|
| (3,4,6) | 2 | 44,817 | **242,113** | 36 |
| (3,4,5) | 2 | 57,404 | **77,613** | 25 |
| (3,4,5,6,7) | 2 | 103 | **312** | 49 |

So between the last run and the last singleton there is a long region with ONLY run-length-1 misses.
My surplus δ·U closes the runs (it bridges length deficits) but CANNOT close a singleton: an isolated
missing point n is not a length deficit — it is a specific VALUE that fails to be representable, i.e.
n ∉ ∑ d^k·B_d as an exact equation. Whether a specific value is hit is residue-equidistribution at
the binding scale = the Mignotte–Waldschmidt core.

**So the honest final form of my leg:**
> **(RUN-BOUND, rigorous-modulo-Baker).** D admissible, gcd(D)=1, ∑1/(d−1)=1+δ>1, gcd(d_max,d_2nd)=1.
> Then no missing RUN of length ≥2 survives above C(δ,D)·(d_max·d_2nd)^k.

This is a clean ELEMENTARY partial (the coarse/length obstruction is fully handled by the margin).
It is NOT cofiniteness — the isolated singletons (run-length-1, value-specific misses) persist to a
larger scale and are the MW core. The surplus-vs-gap (length) argument is provably insufficient for
the single-point misses.

**This is the most precise localization of the open core the measure side has produced:** not just
"internal gaps" but specifically RUN-LENGTH-1 misses — single non-representable values whose locations
are governed by cross-base power equidistribution (MW). The margin handles everything except these.

## TRIANGULATED JOINT LEMMA (with cassels) — T = v = U₀ = gap/σ, with explicit k-dependence

cassels tested my U₀ ~ gap/δ against his +M-closure onset v directly. The triangulation is exact and
it LOCATES my refuted geometric bound precisely within the framework. Verified (σ = δ = harmonic excess):

**The three thresholds are one object:** cassels' +M-closure onset v, my surplus-overtake scale U₀,
and sumset's last-hole are identical, with the relation **U₀ = v ~ gap(D,k)/σ** where gap(D,k) is the
implied alignment gap = v·σ.

**The k-dependence (the precise location of the MW residue):** gap(D,k)/d_max^k for (3,4,5):
| k | N0 | v=N0−3^k | v·σ (=gap) | gap/d_max^k |
|---|---|---|---|---|
| 1 | 79 | 76 | 6.3 | 1.27 |
| 2 | 77,613 | 77,604 | 6467 | **258.68** |
| 3 | 4,330,731 | 4,330,704 | 360,892 | **2887** |

So gap(D,k) = O(d_max^k) PER FIXED k (bounded each k) but with a CONSTANT that GROWS with k for tight
families ((3,4,5): 1.27 → 259 → 2887). For high-σ/many-base families the constant grows slower
((3,4,5,7): 0.68 → 3.5 → 57). **This is exactly why my k-independent geometric bound was refuted:**
the implied constant is k-dependent, and its growth IS the residual MW content.

### The correctly-labeled joint lemma (density surplus + cassels Lemma C)
> **(STRICT-EXCESS, per fixed k, BAKER-CONDITIONAL).** D admissible, gcd(D)=1, ∑1/(d−1)=1+σ>1,
> gcd(d_max,d_2nd)=1. For each FIXED k, T_k(D) is cofinite with threshold N₀ = v + d_min^k, where
> v ~ gap(D,k)/σ. The surplus σ·U overtakes the alignment gap (density's front half) and cassels'
> Lemma C extends elementarily above the seed (back half) — both transcendence-free GIVEN
> gap(D,k) = O(d_max^k). The implied constant in O(d_max^k) is k-dependent (grows for tight D); its
> uniform-in-k boundedness is the residual Mignotte–Waldschmidt content, NOT elementary.

So: PROVEN per-fixed-k (matches cassels' per-fixed-k result); the ONLY non-elementary piece is the
gap-constant's growth with k = uniform-in-k = MW. This supersedes the withdrawn "k-uniform geometric
bound." sumset's "gap = O(d_max^k)" leg must carry the k-dependent-constant flag.

## TWO-EXPONENT PICTURE (with lift) + g*_combined CORRECTION (with sumset)

### lift's two surpluses (joint finding, verified)
There are TWO distinct supercritical exponents, and they diverge at the boundary:
- **Reach/harmonic surplus** δ = ∑1/(d−1) − 1 (my leg) — linear-in-U reach growth, controls the MIN.
- **Counting surplus** ε = ∑(log2/log d) − 1 (lift, REDUCTION_THEOREM Thm 10) — avg representation
  count r_D(n) ~ n^ε, controls the AVERAGE.

**ε > δ STRICTLY** (verified term-by-term: log2/log d > 1/(d−1) ⟺ 2^{d−1} > d, trivial). At the
BOUNDARY (3,4,7): δ = 0 EXACTLY but ε = 0.487 > 0. So avg #reps ~ n^0.487 → ∞ even at the boundary
while the reach-surplus vanishes. Verified: avg-reps local exponent 0.39→0.54 brackets ε=0.487.

**This is the sharpest "why the boundary is critical":** cofiniteness is controlled by the MIN reps
(reach-surplus δ; at boundary δ=0, no slack, MW decides), NOT the AVERAGE (ε>0, →∞ regardless). My
killed INV-D3 was confusing these — min-reps (the right quantity for gaps) vs avg-reps (lift's n^ε,
the wrong quantity, always grows). lift's two-exponent framing correctly separates them.

**FINALIZED as the joint note `note_two_exponents.md` (lift + density, writeup-ready).** Two refinements
lift added there (both adopted): (1) the ε exponent uses the CUMULATIVE/including-zeros average (not
present-only, which is dip-contaminated) — that's the clean k-independent ε. (2) Modest framing per
scholar's prior-art verdict: the ε > δ inequality is folklore and the avg-vs-min distinction is
recognized-but-unnamed (cite Erdős–Tetali / Erdős–Fuchs); the genuinely NEW bit is the
box-counting-dimension (log2/log d) vs Astels-thickness (1/(d−1)) CONTRAST as the structural source
of ε > δ. Data note: (3,4,5,7) ε = 0.918 (corrected from a draft 0.984).

### sumset's g*_combined correction (accepted)
My δ > g* criterion is right but g* must be the COMBINED multi-pair clustering, NOT gcd(top-two):
- gcd(top-two)=1 is the WRONG gate: (5,6,7,8,9,10) top-two (9,10) coprime but worst cluster {6,10}
  gcd=2; (3,4,6) top-two (6,4) gcd=2 but worst cluster {3,4} gcd=1.
- Even single-worst-pair coprimality is insufficient: (3,4,5) is ALL-pairs-coprime, δ=0.083 >
  each single pair's clustering (~0.046), yet threshold GROWS — because the COMBINED multi-pair
  clustering g*_combined exceeds δ even though each individual pair's doesn't.
- So the honest criterion is δ > g*_combined (transcendental in general); whether Baker bounds
  g*_combined uniformly over all pairs simultaneously AND k-uniformly is OPEN (sumset suspects not,
  given (3,4,5)). This SUPERSEDES my gcd(top-two)=1 corner — that gate was both wrong (top-two vs
  worst-pair) and insufficient (single-pair vs combined).

**Net (fully corrected):** the δ > g* recurrence criterion is the right STRUCTURE, but g* is the
combined multi-pair clustering = transcendental; there is no clean elementary gate (not gcd-top-two,
not gcd-worst-pair, not single-pair-Baker). The two-exponent picture (δ reach / ε count) cleanly
explains the min-vs-avg split. These are the correctly-scoped final density findings.

## HYPOTHESIS CORRECTION (cassels) — DROP gcd(d_max,d_2nd)=1 from the joint lemma

cassels caught that my joint-lemma draft carried gcd(d_max,d_2nd)=1, but his chain (Lemma A
gap-condition + lift identity + residue coverage + margin-growth) uses ONLY gcd(D)=1 + σ>0. Resolved
by disentangling two DIFFERENT statements I had conflated:

- **(A) PER-FIXED-K COFINITENESS** (= the joint lemma): T_k cofinite, N₀ = v + d_min^k FINITE for each
  fixed k. {3,4,6} (gcd top-two=2) SATISFIES this: N₀ = 986/242113/58941162, all finite. So (A)
  needs only gcd(D)=1 + σ>0 (+ Baker for gap finiteness) — NOT gcd(d_max,d_2nd)=1. My front-half
  (surplus σ·U overtakes gap) needs gap=O_k(d_max^k) per fixed k, which {3,4,6} ALSO satisfies (gap
  = v·σ = 33/8070/1964705, finite each k). So the front-half does not need gcd(top-two)=1 either.
- **(B) BOUNDED/GEOMETRIC C** (N₀ ≤ C·(d_max·d_2)^k, C controlled): this is where {3,4,6} FAILS and
  where gcd(top-two)=1 was my (sufficient-not-necessary) attempt — but (B) was already REFUTED as
  k-uniform by {3,4,5} and WITHDRAWN.

**RESOLUTION: gcd(d_max,d_2nd)=1 is VESTIGIAL in the joint lemma (A) and is DROPPED.** It belonged
only to the withdrawn geometric-bound claim (B). cassels is right — the joint lemma is strictly more
general without it.

### CANONICAL JOINT LEMMA (co-signed density + cassels, gcd-top-two DROPPED)
> **(STRICT-EXCESS, per fixed k, conditional).** D admissible, gcd(D)=1, σ := ∑1/(d−1) − 1 > 0. For
> each FIXED k, T_k(D) is cofinite with N₀ = v + d_min^k, where v ~ gap(D,k)/σ. The surplus σ·U
> overtakes the alignment gap (density front half) and Lemma C extends elementarily above the seed
> (cassels back half) — transcendence-free GIVEN gap(D,k) = O(d_max^k). The O-constant is k-dependent
> (grows for tight D, e.g. {3,4,6}); its uniform-in-k boundedness is the residual MW. Three names, one
> threshold: cassels' v = density's U₀ = sumset's last-hole = gap/σ + d_min^k.

Note: even (A) is the RUN-version (no missing run ≥2; isolated singletons are the separate MW
interior core, per the runs-vs-singletons finding). And gap(D,k)=O(d_max^k) is itself Baker-conditional.
gcd(d_max,d_2nd)=1 is NOT a hypothesis of the joint lemma — it only governs whether C is BOUNDED
(statement B, withdrawn), which is a strictly stronger and false claim.

## RUN-VS-SINGLETON UNIFICATION (maverick endorsement) — the MW core, concretely

maverick confirmed the decomposition EXACTLY ({3,4,6} k=2: last run≥2 ends 44,817, last singleton =
N₀ = 242,113, both my numbers) and unified it with the whole session's dead routes: the isolated
singletons are the SAME object that killed every other route —
- the Φ=0 large-deviation events at cross-base coincidences (killed INV-C5 + troika's orbit-average),
- the points sumset's M5 non-automaticity guarantees can't be finite-state-described,
- the fat-boundary residual on troika's 2-torus.

So the run-vs-singleton split is the CLEANEST CONCRETE HANDLE on the MW core anyone produced:
> **cofiniteness = (no runs ≥2 above the run-bound, ELEMENTARY/Baker) + (no isolated singletons above
> N₀, MW).** First half = density+carry elementary leg; second half = the irreducible transcendence.

### Final strict-excess leg statement (maverick-endorsed, writeup-ready)
> D admissible, gcd(D)=1, ∑1/(d−1)>1 ⟹ no missing RUN of length ≥2 survives above the run-bound
> (elementary modulo a Baker floor on the run-gap). Cofiniteness additionally needs the isolated
> singletons above N₀ gone = the named MW gap.

Three-front scoping airtight: (hypothesis) gcd(D)=1 + σ>0, with gcd-top-two only governing the
withdrawn bounded-C claim, NOT the run-bound; (bound) conditional, not the fitted 0.27; (conclusion)
runs-not-cofiniteness. For the co-authored high-margin theorem: the RUN-BOUND is the theorem
(elementary), the SINGLETON RESIDUAL is the named MW gap — clean conditional structure.

NEXT DELIVERABLE (for the co-authored framing with maverick): the Baker-floor run-gap derivation —
the explicit bound showing the largest missing run above the run-bound is killed by the surplus σ·U
once the run-gap is bounded via Baker's |d_max^a − d_2^b| floor. maverick co-writes the honest-scope
framing once that derivation is in. The strict-excess leg is otherwise DONE as a precisely-scoped partial.

## BAKER-FLOOR RUN-GAP DERIVATION (the deliverable, with validation)

**Derivation.** A missing RUN of length L ≥ 2 at scale U requires the local reach to fall short by ≥L
over an interval. Runs come from the COARSE structure — the two-largest-scale Frobenius gap, whose
size is bounded by the spacing |d_max^a − d_2^b| of the two largest binding atom-scales at U. By
Baker's lower bound, |d_max^a − d_2^b| ≥ c·max(·)^{1−κ} ~ U^{1−κ} (κ < 1 the Baker exponent), so the
run-gap is **SUBLINEAR: O(U^{1−κ})**. The surplus σ·U is **LINEAR** in U. Hence σ·U > C·U^{1−κ} ⟺
U > (C/σ)^{1/κ} =: X_run; above X_run the surplus dominates every run-gap ⟹ **no missing run of
length ≥ 2 above X_run.** ∎ (Baker-conditional; X_run prefactor is the k-dependent C(D,k), the
residual MW.)

**VALIDATION (C bitset, octave-by-octave max run length).** The mechanism predicts run-length → 0
with scale (sublinear gap killed by linear surplus), while singletons persist longer:
- {3,4,6} k=2, octaves [U,2U]: max_run = 2,2,2,1,1,0 (dies); singletons = 141,112,156,13,42,0
  (persist toward N₀=242,113, then vanish).
- {3,4,5} k=2: max_run = 2,3,3,1,0,0 (dies); singletons = 79,49,118,2,0,0.
Run-length decays to 0 BEFORE singletons vanish — exactly the run-vs-singleton split, and the run
decay is consistent with the Baker-floor sublinear-gap / linear-surplus mechanism. CONFIRMED.

This is the deliverable for the co-authored high-margin theorem: the RUN-BOUND is now derived
(Baker-conditional, validated), with the run-gap sublinearity as the rigorous core and the surplus
σ·U as the linear dominator. The singleton residual (run-length-1 misses persisting to N₀) is the
named MW gap. maverick co-writes the honest-scope framing on this derivation.
