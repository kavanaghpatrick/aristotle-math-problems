# The two supercritical exponents of E124 — reach-surplus δ vs counting-surplus ε

**Authors:** lift + density (joint consolidation note). **Status:** both halves PROVED-elementary;
the headline phenomenon (δ=0 yet ε>0 at the boundary) is the clean explanation of why BEGL96
cofiniteness is *critical* exactly where the representation *count* is still comfortably supercritical.

Notation: D admissible (all d≥3, gcd(D)=1, β:=∑_{d∈D} 1/(d−1) ≥ 1); B_d = {0/1-digit base-d numbers};
R(D,k) = ∑_{d∈D} d^k·B_d the target sumset; A(D,k)={d^j : d∈D, j≥k} the merged atoms.

## Two distinct invariants, two distinct supercritical exponents

The completeness of R(D,k) is governed by TWO different "how much room is there" quantities, which
coincide at k-irrelevant leading order in one sense but carry DIFFERENT exponents:

### (1) The REACH surplus δ (density's leg) — a first-moment / cumulative-mass quantity
Define δ := β − 1 = ∑_{d∈D} 1/(d−1) − 1. At scale U, the combined maximal subset-sum reach of the
atom rays is (1+δ)·U·(1+o(1)); covering [0,U] consumes U, leaving a **surplus reach δ·U**, LINEAR in U.
- δ > 0 (strict excess): surplus δ·U → ∞ outgrows the residual alignment gap, killing all missing
  RUNS of length ≥ 2 above some X₀. [density's (MARGIN-GROWTH) → (RUN-BOUND) lemma,
  density_margin_growth_leg.md; verified: largest upper-half missing RUN bounded, U-independent, to
  N=5·10⁷ even for tiny δ like (3,4,5) δ=0.083 and (4,5,6,7,8) δ=0.093.]
  **SCOPE (corrected — do not overstate; these three caveats are load-bearing):**
  (i) the surplus closes RUNS, not isolated singletons — cofiniteness additionally needs the
  run-length-1 misses gone, which is the MW interior core (density+sumset, runs-vs-singletons).
  (ii) X₀ ≍ gap(D,k)/δ + d_min^k with gap(D,k) = O(d_max^k) PER FIXED k but a k-DEPENDENT constant
  that GROWS for tight families ((3,4,5): N₀/(d_max·d₂)^k = 3.95 → 194 → 541, k=1,2,3). The earlier
  "X₀ ≤ C(δ,D)·(d_max·d₂)^k with C k-independent" was REFUTED (maverick's {3,4,5}) and is WITHDRAWN;
  the constant's uniform-in-k boundedness is itself the residual MW.
  (iii) BAKER-CONDITIONAL (not transcendence-free) wherever a Baker floor on the clustering is used.
- δ = 0 (boundary, e.g. (3,4,7)): NO reach surplus. This is the criticality — the reach exactly
  matches U, no slack to absorb the alignment gap. This is why the boundary needs MW/Baker.

### (2) The COUNTING surplus ε (lift's leg) — a representation-count / convolution exponent
Define e_d := log2/log d (the box/Minkowski-dimension counting exponent of B_d: |B_d∩[0,X]| ≍ X^{e_d}),
and ε := ∑_{d∈D} e_d − 1. The **CUMULATIVE average** #reps over [0,X] — (total #reps of n≤X)/X
= ∏_d|B_d∩[0,X/d^k]|/X — scales as X^{ε}, and ε is k-INDEPENDENT (cassels: log-log slope 0.521 at
k=1, 0.520 at k=2 for (3,4,5)≈ε=0.562). Use the CUMULATIVE/including-zeros average — the present-only
window average is dip-contaminated, a different non-k-independent quantity (cassels' convention). The
MINIMUM r_D (dip envelope c_k·X^ε below the average) is the hard half; c_k = k-dependent dip-depth = N₀(k) residual.
> **Lemma (lift, elementary — folklore-flavored).** e_d > 1/(d−1) for every d ≥ 3. Proof:
> log2/log d > 1/(d−1) ⟺ (d−1)log2 > log d ⟺ **2^{d−1} > d** (trivial Nat induction, equality at d=2).
> Hence **ε = ∑ e_d − 1 > ∑ 1/(d−1) − 1 = δ ≥ 0 STRICTLY.**
So **ε > δ always**, and **ε > 0 even at the boundary δ=0** ((3,4,7): δ=0, ε=0.487). The cumulative-avg
~X^ε is a clean lattice-point count (deductively provable); only the min-vs-avg dip is residual.
[lift_box_reformulation.md; REDUCTION_THEOREM Theorem 10.]

> **Prior-art framing (scholar's verdict — present MODESTLY):** (1) e_d>1/(d−1) is FOLKLORE (one-line
> convexity). (2) "avg supercritical but min dips at coincidences" is recognized-but-unnamed — nearest:
> Erdős–Tetali (avg r(n)), Erdős–Fuchs (L² fluctuation of r(n)); cite as closest recognized work, NOT
> our coinage. (3) The GENUINELY NEW bit = the CONTRAST: counting/box-dimension e_d=log2/logd vs
> completeness/Astels-thickness 1/(d−1) — both classical individually (box dimension; Astels 2000),
> NEVER juxtaposed for {B_d} to explain avg-supercritical-while-completeness-critical. Cite Erdős–Tetali
> + Erdős–Fuchs + Astels + box-dimension classics (verify exact refs via MathSciNet). Synthesis is the contribution.

## The headline phenomenon: δ = 0 yet ε > 0

| family | δ = β−1 (reach) | ε = ∑(log2/logd)−1 (count) | reading |
|---|---|---|---|
| (3,4,7) | **0.000** | **0.487** | boundary: NO reach surplus, but avg #reps→∞ |
| (3,5,7,13) | 0.000 | 0.688 | boundary: same |
| (3,4,5) | 0.083 | 0.562 | strict: both positive |
| (3,4,5,7) | 0.250 | 0.918 | strict: both larger |

**The clean explanation of why BEGL96 is hard exactly at the boundary:** cofiniteness is governed by
the REACH (δ) — at δ=0 there is zero slack, so whether the alignment gap closes is a knife-edge
Diophantine question (MW). But the representation COUNT is governed by ε > 0 even there — so the
AVERAGE number of representations of large n still diverges (n^{0.487} for (3,4,7)). The conjecture is
TRUE-looking because ε>0 makes representations abundant on average; it is HARD because δ=0 means the
MINIMUM (not the average) is what must be controlled, and the minimum dips at the cross-base
power-coincidences where the reach-surplus is locally exhausted.

**In one line:** *the boundary β=1 is critical for the reach (δ=0) but supercritical for the count
(ε>0); BEGL96's difficulty is exactly the gap between "average count → ∞" (free, ε>0) and "minimum
count ≥ 1" (the open core, controlled by the δ=0 reach criticality at power-coincidences).*

## Why ε > δ (the structural reason, not just the inequality)

1/(d−1) = ∑_{j≥1} d^{−j} is the geometric ENVELOPE of one ray's reach density (the fraction of [0,X]
a single base-d ray's subset-sums can cover). e_d = log2/log d is the box/counting DIMENSION of B_d
(governing how many subset-sums land in [0,X]). The counting dimension always exceeds the reach
density for d ≥ 3 because B_d is "fatter in count than in reach" — there are more 0/1-digit numbers
than the linear reach suggests, but they overlap/collide when summed. The gap ε − δ > 0 is precisely
this count-vs-reach discrepancy, and it is what keeps the average count supercritical at the reach
boundary.

## Status / use

- Both exponents PROVED-elementary (δ: definition + Pomerance; ε > δ: the 2^{d−1}>d lemma).
- The reach side (δ) drives density's strict-excess (MARGIN-GROWTH) lemma → the per-fixed-k
  strict-excess theorem (with cassels).
- The count side (ε) drives lift's (KERNEL): cofinite ⟺ min r_D ≥ 1, with avg r_D ~ n^ε → ∞ proved.
- The note's value for the writeup: it is the cleanest published-quality articulation of WHY the
  boundary is the hard case — a one-table, two-exponent statement, fully elementary, no transcendence,
  that frames exactly what MW must supply (the min-vs-avg gap at δ=0).

Cross-refs: density_margin_growth_leg.md (δ leg), lift_box_reformulation.md + REDUCTION_THEOREM
Theorem 10 (ε leg), lift_boundary_criticality.md (the criticality at δ=0).
