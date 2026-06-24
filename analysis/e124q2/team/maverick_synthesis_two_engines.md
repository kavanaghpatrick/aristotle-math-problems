# maverick: the unified two-engine mechanism + the REAL obstruction (β_total→0)

Synthesizes [[sumset_reduction_scaling]] (sumset), [[modular_local_coverage]] (modular),
[[lift_sufficiency_mechanism]] (lift), [[scholar_BEGL96_proof_dissected]] (scholar),
and my [[maverick_recursion_engine]].

Notation: atoms `A(D,k) = { d^j : d∈D, j≥k }` (with multiplicity over (d,j)); the open problem
(carry's clean form, verified) is: **is A(D,k) a complete sequence** — i.e. is the distinct-atom
subset-sum set `T_k = ∑_{d∈D} d^k·B_d` cofinite, for every admissible D (all d≥3, ∑1/(d−1)≥1,
gcd(D)=1) and every k≥1?

## THE REAL OBSTRUCTION (new, quantitative — this is why k≥2 is genuinely hard)

The total reciprocal mass of the atoms is
> `β_total(k) := ∑_{atoms b} 1/b = ∑_{d∈D} d^{1−k}/(d−1)`.

**At k=1:** `β_total(1) = ∑_d 1/(d−1)` = exactly the harmonic condition (≥1). ✓
**At k≥2:** `β_total(k) = ∑_d d^{1−k}/(d−1) → 0 geometrically** (like d_min^{1−k}).

Computed (verified):

| D | β_total(1) | β_total(2) | β_total(3) | β_total(4) |
|---|-----------|-----------|-----------|-----------|
| {3,4,7} | 1.000 | 0.274 | 0.080 | 0.024 |
| {3,4,5} | 1.083 | 0.300 | 0.086 | 0.026 |
| {4,5,6,7,8} | 1.093 | 0.208 | 0.042 | 0.009 |

**Consequence (kills the naive density route):** Scholar's Claim 1 (Cassels-type gap bound)
needs a finite chunk with reciprocal sum `β > 2`. The atoms' TOTAL reciprocal mass is < 1 for
every k≥2 — you can never assemble a chunk with β>2. **So for k≥2 the completeness of A(D,k)
is NOT explained by "large reciprocal sum."** A complete sequence here has reciprocal mass → 0.
This is the precise sense in which the open problem at k≥2 is harder than k=0/k=1 and why
BEGL96's general machinery (which is reciprocal-mass / positive-density driven) does not reach it.

## WHAT ACTUALLY MAKES IT COMPLETE (verified two-engine synthesis)

### Engine 1 — bounded gaps (interval engine). VERIFIED.
Build the subset-sum set by adding atoms in ascending order. The **max gap stabilizes at a
constant G(k)**, not at ∞:

| D | G(1) | G(2) | G(3) |
|---|------|------|------|
| {3,4,5} | 3 | 9 | 37 |
| {3,4,7} | 3 | 9 | 71 |
| {4,5,6,7,8} | 4 | 16 | 64 |

For the {4,5,6,7,8} family **G(k) = d_min^k EXACTLY** (k=1,2,3). For d_min=3 families G(k)=d_min^k
for k≤2 and slightly exceeds it at k=3. **Why bounded despite β_total→0:** each base contributes a
geometric ladder d^k, d^{k+1}, … with ratio d; consecutive atoms of one base never outrun that
base's own running sum by more than a bounded factor, so the *partial* sums dominate the *next*
atom after a finite transient (scholar's Claim 1 facts (a),(b) hold ladder-by-ladder, which needs
only β>0, NOT β>2 — the >2 was for the cruder general bound). The smallest atom d_min^k sets the
gap scale.

**This is the key correction to the density narrative:** bounded gaps need β_total>0 (always true),
not β_total>2. The Cassels β>2 was sufficient-but-wasteful; the ladder structure does better.

### Engine 2 — residue coverage. VERIFIED (modular's (L), re-confirmed by me).
gcd(D)=1 ⟹ T_k ≡ ℤ/m for every m. So every residue class is *eventually* populated.

### The synthesis (the actual closing argument)
Engine 1 alone gives: for n ≥ X1(k), every window [n, n+G(k)) contains a representable point —
but possibly only ONE, so non-representable n persist (gaps up to G(k)). Engine 2 alone gives:
every residue is hit, but with no control on *where*. **Cofiniteness = the threshold n₀(k) beyond
which the residue classes are ALL populated densely enough that the ≤G(k) gaps are fully filled.**
The misses just below n₀(k) are spread across all residues mod d_min^k (verified: for {3,4,5} k=2
the 1128 misses are ~evenly distributed over all 9 classes mod 9) — confirming the obstruction is
the *joint* interaction, not a single stuck residue.

## What a PROOF must therefore supply (the genuine open core, sharpened)
A bound, **uniform in k**, of the form: *for n ≥ n₀(k), the subset-sum set T_k has no gap.* The two
verified ingredients reduce this to: **(★) effective bound on n₀(k) showing every residue class mod
G(k) is represented by some element of T_k in every window of length C·G(k), for n ≥ n₀(k).**
This is a quantitative equidistribution statement about base-d 0/1-digit sets under CRT coupling —
exactly the analytic core BEGL96 solved only for (3,4,7) via Mignotte–Waldschmidt linear forms in
logs (controlling |d_i^p − d_j^q|). For general admissible D this is OPEN.

## Honest bottom line
- Reduction, local lemma, recursion, bounded-gap engine: **all VERIFIED** (mine + peers, cross-checked).
- Answer is almost certainly **True** (BEGL96 conjecture holds): every admissible family tested is
  cofinite at k=1,2 with finite thresholds; both side-conditions provably necessary.
- The remaining gap (★) is a real analytic/transcendence problem (linear forms in logs for general
  base pairs), NOT a formalization gap. No finite computation closes it (n₀(k)→∞, verified
  79→77613→4.3M→69M for {3,4,5}). This is the same wall BEGL96 hit and called "still fairly far."
