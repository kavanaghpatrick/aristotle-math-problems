# forge — EXTREMAL/STABILITY lane: the E*-degree bound (with jensen, 2026-06-11)

Question (team-lead's extremal lane): what does almost-zero |E*| force structurally,
seeded from the proven floor |E*| ≥ ⌈n/2⌉?

## Finding 1: the ⌈n/2⌉ floor is FAR from tight
Exhaustive min |E*| over all 4-vertex-critical graphs:
| n | floor ⌈n/2⌉ | actual min |E*| | gap | E*-maxdeg at minimizer |
|---|---|---|---|---|
| 7 | 4 | 7 | +3 | 2 |
| 8 | 4 | 12 | +8 | 4 |
| 9 | 5 | 9 | +4 | 3 |
The minimizers do NOT approach the edge-cover floor, and E* is NEVER a matching
(maxdeg ≥2 always). So the witness is not "approached" by a sequence of near-extremal
graphs with E* shrinking to a matching — E* stays dense and connected.

## Finding 2 (the gold): a DEGREE-DEPENDENT E*-degree lower bound, k=4-specific
For each vertex v, E*-deg(v) = #critical edges at v. Exhaustive min over ALL
4-vertex-critical graphs n=7,8,9 (1229 vertices):
| graph-deg(v) | MIN E*-deg(v) observed |
|---|---|
| 3 | 3 |
| 4 | 2 |
| 5 | 1 |
| 6 | 1 |
| (7) | 7 (single sample) |
**Pattern: E*-deg(v) ≥ max(1, 6 − deg(v))** — exact for deg 3,4,5; floors at 1 for
deg ≥ 6. Never 0 at any degree (= vertex-spanning).
- deg 3 → ≥3 is exactly forge's deg-3 theorem (all 3 edges critical).
- deg 4 → ≥2, deg 5 → ≥1 are the new sloped extension.
- deg 6 → ≥1 is the crux: a witness needs E*-deg 0 at every vertex, but a deg-6
  vertex is observed to always have ≥1 critical edge.

## k=5 CHECK (wall's filter — PASSES, genuinely k=4-specific)
The k=5 analogue would be E*-deg(v) ≥ max(1, 2(k−1) − deg(v)) = max(1, 8−deg). At
deg=8 this gives ≥1. But the k=5 witness G_5,2,2 is 8-REGULAR with |E*|=0 ⟹ E*-deg
0 at every deg-8 vertex ⟹ the bound is FALSE at k=5. So the k=4 bound "deg-6 ⟹
E*-deg ≥1" genuinely BREAKS at k=5 — it is k=4-specific, passing wall's filter.
(Contrast: my plain vertex-spanning statement is generic and also "breaks" at k=5
only because witnesses exist, not because the PROOF is k=4-specific. The E*-degree
SLOPE 6−deg is tied to q=3 = 3 colors specifically.)

## Why the slope is q=3-specific (the mechanism)
At vertex v, in a proper 3-coloring of G−v, N(v) splits into 3 color classes
(a,b,c), a+b+c = deg(v). v is colorable (no forced 4th color) iff all 3 classes
≥1. A color class of size 1 (singleton) ⟹ the edge v–(that carrier) is critical
(forge per-vertex lemma). With deg(v) = d and 3 classes, the MINIMUM number of
singleton-classes over the worst coloring relates to how unbalanced N(v) must be.
For d=3: forced (1,1,1) ⟹ 3 singletons ⟹ 3 critical. d=4: best is (2,1,1) ⟹ ≥2
singletons in the worst case ⟹ ≥2 critical. d=5: (2,2,1) ⟹ ≥1. d=6: (2,2,2)
ACHIEVABLE (balanced) ⟹ the per-coloring bound gives 0 — BUT the GLOBAL condition
(every coloring of G−v balanced) is what fails, forcing ≥1. THIS is exactly the
gap between the local pigeonhole (closes deg<6) and the global CSP (deg≥6,
gallai's Thm 4). The slope 6−deg is the LOCAL pigeonhole; the deg-6 floor of 1 is
the GLOBAL part nobody has closed.

## STATUS (honest)
- deg ≤ 5: the bound E*-deg ≥ 6−deg is the LOCAL pigeonhole (each deg-d vertex with
  3 classes is forced to have ≥ 6−d singleton classes in its worst coloring). This
  is PROVABLE locally and k=4-specific (3 classes). I'll formalize it with jensen.
- deg ≥ 6: the floor "≥1" (= vertex-spanning at deg-6 vertices) is the GLOBAL CSP
  core (gallai Thm 4) — NOT closed. The witness lives entirely in the δ≥6 regime,
  so the local slope doesn't reach it; the global part is the whole difficulty.
- VALUE: the slope cleanly explains WHY low-degree vertices are forbidden (giving
  δ≥6 from a finer per-degree count than just "δ≥4") and isolates the irreducible
  core to the deg≥6/2-2-2 regime — a cleaner statement of the gap than before.
  Verify to n≥31 (wall's lesson) before asserting the slope as a theorem.

## LOCAL LEMMA — PROVABLE, k=4-specific (the new provable piece)
> **Lemma (forge, local E*-degree slope).** In a 4-vertex-critical graph, a vertex
> v of degree d satisfies E*-deg(v) ≥ max(0, 6−d) — i.e. ≥ (6−d) of its edges are
> critical, for d ≤ 6.
>
> Proof. v is vertex-critical ⟹ G−v is 3-colorable; fix any proper 3-coloring c.
> Since G is 4-chromatic, c cannot extend to v ⟹ N(v) meets all 3 colors ⟹ N(v)
> partitions into 3 NONEMPTY color classes of sizes summing to d. The number of
> size-1 classes (singletons) in such a partition is ≥ (number of parts forced to
> be 1) = max(0, 6−d) [since 3 nonempty parts summing to d minimize their singleton
> count by being as balanced as possible: d=3→(1,1,1), 3 singletons; d=4→(2,1,1),
> 2; d=5→(2,2,1), 1; d≥6→(2,2,2)-able, 0]. Each singleton color's unique carrier w
> gives a critical edge vw (forge per-vertex lemma: color c(w) appears once in N(v)
> ⟹ recolor v with c(w) in G−vw ⟹ G−vw 3-colorable ⟹ vw critical). So in THIS
> coloring ≥ max(0,6−d) neighbors are singleton-carriers, hence ≥ max(0,6−d) edges
> at v are critical. ∎
>
> Verified: holds universally, 0 violations over 1229 vertices (n=7,8,9); tight at
> the minimum for each degree (deg-3 always =3; deg-4 min 2; deg-5 min 1).

k=4-SPECIFICITY: the bound is "partition d into 3 nonempty parts, count forced
singletons" — the "3" is the q=3 = 3 colors. At k=5 (q=4): partition into 4
nonempty parts, forced singletons = max(0, 8−d); at d=8 (G_5,2,2's degree) this is
0 — consistent with G_5,2,2 having E*-deg 0 (no critical edge). So the slope is
genuinely q-indexed; the k=4 version forbids E*-deg 0 only up to d=5, and d≥6 is
the open global core. This PASSES wall's k=5 filter cleanly (the proof uses "3
nonempty parts," which becomes "4 nonempty parts" at k=5 and gives the correct
weaker bound — so it would NOT wrongly prove |E*|≥1 at k=5).

## WHAT THIS BUYS (honest)
- A clean, PROVEN, k=4-specific local lemma: deg ≤ 5 vertices each force ≥(6−deg)
  critical edges. Generalizes the deg-3 theorem to a slope. Gives δ≥6 for a witness
  from a finer count (any deg≤5 vertex ⟹ a critical edge).
- It does NOT close the witness question: the witness is δ≥6 (all degrees ≥6), where
  the local bound gives 0 forced singletons-per-coloring (2-2-2 achievable). The
  deg≥6 floor of "≥1 critical edge" (vertex-spanning) is the GLOBAL CSP — the local
  lemma stops exactly at the hard boundary. Same irreducible core (gallai Thm 4).
- VALUE: cleanest statement of WHERE local arguments die — precisely at the 2-2-2
  balance point d=6. The whole difficulty is the single question: can a deg-6 vertex
  be 2-2-2-balanced in EVERY 3-coloring of G−v, globally? (Local says yes per-coloring;
  global says no, unproven.)

## DEATH POINT (kill-fast, 2026-06-11): the slope is TIGHT — no stronger local bound
Tested whether deg-6 vertices force E*-deg ≥2 (which would give |E*|≥n for 6-regular,
stronger than vertex-spanning's n/2). FALSE: 6 deg-6 vertices at n≤9 (e.g. n=9 minimizer
HCp`fzy) have E*-deg EXACTLY 1. C13(1,2,5)'s uniform E*-deg=2 is a regularity artifact,
not forced. So the slope bound E*-deg ≥ max(0,6−deg) is TIGHT at every degree, and the
deg-6 floor is exactly 1 (= vertex-spanning, the global core). NO stronger local bound
exists. The stability lane's local story is COMPLETE; the deg-6/2-2-2 floor is the
irreducible global CSP (gallai Thm 4) — per team-lead's ruling, NOT to be ground on
locally. Stability lane conclusion: proven slope lemma (local, tight, k=4-specific) +
the deg-6 floor=1 is exactly the global boundary. Local toolkit saturated here.

## COMPLETE EXTREMAL FRONTIER (n≤10, exhaustive)
| n | floor ⌈n/2⌉ | min |E*| | gap | minimizer E*-maxdeg | E* matching? | E* components |
|---|---|---|---|---|---|---|
| 4 | 2 | 6 | +4 | (K4) | no | 1 |
| 7 | 4 | 7 | +3 | 2 | no | 1 |
| 8 | 4 | 12 | +8 | 4 | no | 1 |
| 9 | 5 | 9 | +4 | 3 | no | 1 |
| 10 | 5 | **8** | +3 | 2 | no | **2** |
n=10 minimizers (|E*|=8): g6 ICpdbY{]_, ICpddxy^?, ICpdlps]_ — degree sequences heavy
on degree-5 (e.g. [5,5,5,5,5,5,...] and [5,5,5,5,4,4,...]), E* in 2 components, spanning,
maxdeg 2. So the extremal minimizers are δ=4–5 (NOT yet δ≥6), E* spanning but disconnected.
STABILITY READ: min |E*| stays well above ⌈n/2⌉; E* is never a matching and is sometimes
disconnected (2 comps at n=10) — so a near-witness is NOT approached by E* thinning to a
matching, and the |E*|-extremal graphs are NOT 6-regular (they have degree-4/5 vertices,
which by the slope lemma each carry ≥1–2 critical edges — that's WHY their |E*| can't drop
to the floor). To push |E*| lower you need δ≥6 (eliminate the slope-forced edges), but then
the deg-6 global floor (≥1 each) takes over. The two regimes (slope-forced low-degree edges
vs global deg-6 floor) together keep |E*| bounded away from 0 — the full local picture.

## §2b FINAL — the E*-degree slope lemma (k-indexed, independently verified n≤31)
INDEPENDENT VERIFICATION (jensen, verify_estar_slope.py, 2-engine χ, distinct harness):
0 violations / 216 vertices — complete n≤7 census + Grötzsch n=11 + circulants C_n(1,2,5)
at n=13,16,19,25,31 (wall's n≥31 push) + the n=19,23 plateau seeds. TIGHT at deg≤5 (46/59
census vertices tight). Assertable.

> **LEMMA (E*-degree slope, k-indexed).** Let G be a k-vertex-critical graph (χ=k,
> every vertex critical). For every vertex v, the number of critical edges incident
> to v satisfies
>     E*-deg(v) ≥ max(0, 2(k−1) − deg(v)).
> Proof. v critical ⟹ G−v is (k−1)-colorable; fix any proper (k−1)-coloring c. χ=k
> ⟹ c does not extend to v ⟹ N(v) meets all k−1 colors ⟹ N(v) partitions into k−1
> NONEMPTY color classes summing to deg(v). The number of size-1 classes (singletons)
> in such a partition is ≥ max(0, 2(k−1) − deg(v)) [to avoid singletons all k−1 parts
> need size ≥2, i.e. deg(v) ≥ 2(k−1); below that, ≥ 2(k−1)−deg parts are forced to
> size 1]. Each singleton color's unique carrier w gives a critical edge vw (per-vertex
> lemma: c(w) appears once in N(v) ⟹ recolor v with c(w) in G−vw ⟹ (k−1)-colorable
> ⟹ vw critical). So ≥ max(0, 2(k−1)−deg(v)) edges at v are critical. ∎
>
> **k=4 form:** E*-deg(v) ≥ max(0, 6−deg(v)). **Corollary:** a (4,1)-witness has
> δ≥6 (any deg≤5 vertex forces a critical edge) AND every vertex is (k−1)-balanced
> (all classes ≥2) in SOME (k−1)-coloring of G−v.

k=5 FILTER (wall): at k=5 the bound is max(0, 8−deg); deg-8 (G_5,2,2) → 0, consistent
with the genuine (5,1)-witness's |E*|=0. The proof's "k−1 nonempty parts" auto-indexes
with k, so it CANNOT wrongly prove |E*|≥1 at k=5. Genuinely k-indexed / k=4-specific.

THE BOUNDARY (open core, jensen's subsection): the slope is 0 at deg ≥ 2(k−1) (=6 for
k=4), i.e. (k−1)-balanced partitions exist PER coloring there. A witness needs every
vertex balanced in EVERY (k−1)-coloring of G−v SIMULTANEOUSLY — the irreducibly global
q=k−1 CSP (gallai Thm 4). The local lemma's content is the per-coloring floor; the
global "every-coloring" upgrade is the whole remaining difficulty, untouched by local
arguments. STATUS: §2b proven + independently verified; the boundary is the stated open core.

## §2b SHARPNESS (jensen's nuance, forge-verified): the bound PARTITIONS, not just bounds
The slope lemma's content is sharpest stated as a PARTITION, not a bound. Two kinds of "tight":
- TRIVIAL tight (fully edge-critical graphs, e.g. Grötzsch): E*-deg(v)=deg(v) ≥ bound,
  tight at deg-3 but only because ALL edges are critical — the lemma constrains nothing.
- INFORMATIVE tight (MIXED graphs with non-critical edges): at a tight low-degree vertex
  the bound EXACTLY PARTITIONS the incident edges. VERIFIED on n=9 minimizer HCp`fzy
  (mixed, |E*|=9/19): every tight deg-4 vertex has EXACTLY 2 critical + 2 non-critical
  incident edges = the bound (2) forces 2 critical and PERMITS the other 2 non-critical.
  (Cross-checked on wall's n=19 seed by jensen: deg-4 tight ⟹ 2 crit + 2 non-crit.)

So the real statement: **a vertex of degree d < 2(k−1) CANNOT have all its incident
edges non-critical — at least 2(k−1)−d of them are FORCED critical.** A (4,1)-witness
needs ALL edges non-critical at EVERY vertex ⟹ every vertex has degree ≥ 6 ⟹ δ≥6
(the corollary, now with the sharp "partition" mechanism: the witness must sit at the
slope's ZERO — degree ≥ 2(k−1) — at every vertex, which is exactly where the local
floor permits all-non-critical, and then the GLOBAL every-coloring-balanced question
takes over). Local half DONE + verified to n=31; deg-6 simultaneity is the last standing piece.
