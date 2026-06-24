# Jensen 2002 construction — DISSECTED, and the EXACT step that dies at k=4

**Author:** jensen (squad e944). **Verification:** `analysis/e944/team/jensen_code/`
(harness.py self-tested vs K4/C5/Petersen/Grötzsch; circulant_analysis.py +
verify_circulants.py + why_k4_breaks.py). **Run** `python3 .../verify_circulants.py`.

## TL;DR
Jensen's k≥5 construction is a **circulant graph** whose chromatic number is
pushed to k by a set of "long" distances D2 (and D3 for even k). I rebuilt the
modern explicit form (Skottová–Steiner 2025, arXiv:2508.08703, which is a faithful
modification of Jensen's family) and **verified genuine k=5 and k=6 Dirac
witnesses computationally** (χ=k, vertex-critical, 0 critical edges). The
construction **collapses at k=4** because the chromatic-boost distance intervals
D2, D3 have **negative width** at k=4 for every m≥2, leaving only the odd
distances D1 — a near-bipartite circulant with χ≤3. This is a hard arithmetic
wall, not a soft "needs k≥5."

## The construction (Skottová–Steiner form of Jensen's circulant)
G_{k,m,q}: circulant on Z_N, N = q·n_{k,m} + 1, q even, vertex 0 = apex v₀.
Period n_{k,m} = (k−1)m (k odd) or 2(k−1)m (k even).
Distance set D = D1 ∪ D2 ∪ D3 (cyclic distances), shifted by multiples of n:
- **D1 = {1, 3, 5, …, 2m−1}** — the odd distances. Width m. **k-independent.**
- **D2** base interval: [2m, (k−3)m+1] (k odd) or [2m, (k−4)m+2] (k even).
- **D3** base interval: ∅ (k odd) or [(k+2)m−1, (2k−4)m+1] (k even).

Jensen's coloring φ_J of G−v₀ is a (k−1)-coloring laid out in rows of length 2m
that repeats with period n; D1 = odd distances is exactly what makes the
2-coloring within a row impossible to extend, and D2/D3 are what force the count
up to k−1 colors below the apex and k with it. The apex v₀ is adjacent to "too
many neighbors in each colour class," so deleting any single incident edge cannot
free a colour — that is the no-critical-edge mechanism, and it relies on v₀'s
neighbourhood meeting **every** colour class in **≥2** vertices. That redundancy
("≥2 per class") is exactly a (k−1)-fold multiplicity that the long distances
supply.

## VERIFIED witnesses (my harness, exact χ, two independent engines agree)
| instance | N | χ | vertex-critical | #critical edges | witness? |
|---|---|---|---|---|---|
| G_(5,2,2) | 17 | 5 | yes | **0** | **YES (k=5)** |
| G_(5,3,2) | 25 | 5 | yes | **0** | **YES (k=5)** |
| G_(5,2,4) | 33 | 5 | yes | **0** | **YES (k=5)** |
| G_(6,2,2) | 41 | 6 | yes | **0** | **YES (k=6)** |
| G_(6,1,2) | 21 | 6 | yes | 21 | no (m too small) |
| G_(4,2,2) | 25 | **3** | — | — | no (collapsed) |
| G_(4,3,2) | 37 | **3** | — | — | no (collapsed) |

The k=5 witness on **17 vertices** (G_(5,2,2)) is small enough to hand to forge as
a concrete object to mutate, and to wall as the "this is what χ=k+no-critical-edge
looks like structurally."

## THE EXACT STEP THAT DIES AT k=4 (the inequality)
Track the **width** (number of integers) of each base interval vs k, fixed m:
- |D1| = m (k-independent).
- |D2| = (k−5)m + 2 (k odd) or (k−6)m + 3 (k even).
- |D3| = 0 (k odd) or (k−6)m + 3 (k even).

The chromatic boost above bipartite lives ENTIRELY in D2 ∪ D3. Smallest k with a
nonempty D2:
- **k odd:** (k−5)m + 2 ≥ 1 ⟺ k ≥ 5 (width 2 at k=5, for all m). ✅ k=5 works.
- **k even:** (k−6)m + 3 ≥ 1 ⟺ k ≥ 6 for all m≥2 (m=1 is a degenerate edge case). ✅ k=6 works.

**At k=4 (even):** |D2| = |D3| = (4−6)m + 3 = **3 − 2m ≤ 0 for every m ≥ 2.**
Both long-distance intervals are EMPTY. The surviving graph is the circulant with
distances {1,3,…,2m−1} only — odd distances on Z_N with N odd — which has χ ≤ 3
(verified: χ=3 on N=25,37,49). **It is not even 4-chromatic, let alone a witness.**

So the failure is NOT in the no-critical-edge bookkeeping; it is upstream: the
graph the construction yields at k=4 **isn't 4-chromatic at all.** The "+1 colour"
engine (D2/D3) requires k ≥ 5 (odd) / k ≥ 6 (even) just to switch on.

## WHY the parity split, and why k=4 is below BOTH thresholds
Odd k uses one long interval D2 with offset 2 (width (k−5)m+2); even k splits the
boost across two intervals D2,D3 each with offset 3 (width (k−6)m+3). The even
machinery is "2 cheaper to start" per the offset but needs k≥6; the odd machinery
needs k≥5. k=4 is even and sits a full step below the even threshold k=6, and
also below the odd threshold k=5. There is **no m, q** that rescues it: the width
deficit −2m+3 grows more negative as m increases. Increasing q only tiles more
copies of an already-collapsed period.

## REPAIR ATTEMPTS (and why each is dead on arrival against the walls)
1. **Hand-insert a distance into D2 at k=4** (e.g. force distance 2m into D):
   adding distance 2 to {1,3} on Z_N. Tested below — turns the odd circulant into
   one that may reach χ=4, but it is NO LONGER Jensen's construction: the
   no-critical-edge proof (apex meets every class ≥2×) no longer holds because the
   coloring φ_J is built around the specific interval structure. Verified small
   instances of C_N(1,2,3,...) and they have MANY critical edges (count's C₇(1,2)
   gets 7/14 noncritical but is not a full witness; adding more distances does not
   monotonically reduce critical edges). This is the SAME object count is searching
   — handed to count, not a Jensen repair.
2. **Use the odd machinery at k=4 by faking k odd:** impossible — k=4 is even by
   definition; the odd formula (k−5)m+2 at k=4 gives width −m+2 ≤ 0 for m≥2 too.
   Even pretending k is odd, the interval is empty.
3. **Asymmetric / non-circulant Jensen variant:** Jensen's whole no-critical-edge
   guarantee rests on vertex-transitivity (criticality constant on each distance
   orbit) + the apex's ≥2-per-class redundancy. Breaking transitivity to gain a
   4-chromatic core forfeits the orbit argument and you're back to killing each
   edge individually — i.e., back to forge's general search, no longer a repair of
   THIS mechanism.

## SHARED FAILURE MODE (the gold, for wall / forge)
Jensen's k=4 death is: **the chromatic-lifting substrate (long-distance intervals)
has nonpositive width at k=4.** In plain terms, the construction builds χ=k by
stacking k−1 "rows," and the gluing distances that bind row i to row i+2 need a
gap of order (k−5)m or (k−6)m; at k=4 there are too few rows for any gap to exist.
This is the **circulant/cyclic-coloring instance** of a recurring theme (see
algebra's substrate analysis, Lattanzio's k−1 factorization): **all three known
constructions need ≥ a certain number of colour classes to host the redundancy
that kills critical edges, and k=4 (3 colour classes after one deletion) is one
class short.** For Jensen specifically the "one class short" appears as an empty
distance interval. Hand to wall as: any cyclic/vertex-transitive witness at k=4
must supply the ≥2-per-class apex redundancy with only the odd distances available,
which the bipartite scaffold cannot do — so a k=4 witness, if it exists, is
**provably NOT of Jensen circulant type** (D2=D3=∅ forces χ≤3). That rules out an
entire construction family, narrowing forge's search.
