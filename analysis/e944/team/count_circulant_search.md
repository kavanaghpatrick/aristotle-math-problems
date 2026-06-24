# E944 — Circulant (4,1)-witness search: exhaustive over distance sets (count)

**Bottom line:** No circulant (4,1)-graph exists in any of the ranges searched.
This **independently corroborates and substantially strengthens** Steiner's
published lean (Skottova–Steiner 2025, arXiv:2508.08703 §5) that circulant
(4,1)-graphs probably don't exist — Steiner only ruled out his specific
distance-set family D1={1..2m−1} (which forces χ=3 at k=4); I tested **arbitrary**
distance sets meeting Prop 5.1.

## What was searched (exact, reproducible)
Engine `critedge.py` (exact DSATUR chi, self-tested vs brute force).
Vertex-transitivity exploited: criticality is constant on each difference-orbit,
so a circulant is a witness iff χ=4, vertex 0 critical, and EVERY difference
yields a non-critical edge.

| search | files | range | # 4-vtx-critical circulants examined | witnesses |
|---|---|---|---|---|
| all distance sets, \|S\|≤5 (any degree) | circulant_search.py | n=4..22 | 143 | **0** |
| 6-regular (\|S\|=3, Prop-5.1-compliant) | circulant_6reg_search.py | n=11..40 | 610 | **0** |
| degree≥6 (\|S\|=3,4, incl. degree-8) | circulant_6reg_search.py nonreg | n=11..24 | 103 | **0** (best still C₁₃(1,2,5)) |

## The mechanism, now sharply diagnosed
**Best approximate witness overall: C₁₃(1,2,5)** — 6-regular, n=13, 39 edges,
4-vertex-critical. Critical-edge breakdown by difference-orbit:

| difference orbit | # edges | χ(G − one edge) | critical? |
|---|---|---|---|
| 1 (outer Hamilton cycle) | 13 | 3 | **CRITICAL** |
| 2 | 13 | 4 | non-critical |
| 5 | 13 | 4 | non-critical |

So **26 of 39 edges (2/3) are non-critical**; it fails ONLY on the difference-1
orbit. Same shape as C₇(1,2) (which failed only on its difference-1 orbit).

**Structural reading:** across these circulants the *spanning short cycle*
(difference 1) is the stubborn critical orbit. Intuition: the difference-1 edges
form the unique Hamilton cycle that "carries" the odd-girth obstruction forcing
χ=4; removing one of them opens a 3-coloring. The longer-distance orbits are
redundant for the chromatic obstruction, hence non-critical. A witness would need
the short-cycle obstruction to also be redundant — no 3-element (or tested
4-element) Z_n distance set achieves this.

## Why this is decisive intel for the squad
- **The circulant route is now empirically closed up to n=40 (6-regular) over ALL
  distance sets, not just Steiner's family.** If a (4,1)-graph exists it is very
  likely NOT a circulant — which means forge/hunter should not waste cycles on
  circulant constructions, and should target NON-circulant vertex-transitive or
  asymmetric 6-regular graphs (Cayley graphs of non-cyclic groups, or ad-hoc).
- The "1 critical orbit short" plateau (C₇(1,2), C₁₃(1,2,5)) is the
  signature of the difficulty: circulants get *almost* there but the Hamilton-
  cycle orbit always survives.
- This does NOT bear on the TRUE/FALSE verdict for general graphs. Steiner
  explicitly makes NO general non-existence conjecture; a witness could be a
  non-circulant 6-regular graph (his Problem 5.2 remains open). hunter/forge own
  that broader search.

## Cross-check requested
- archivist/algebra: is the Brown k=5 witness a Cayley graph of a NON-cyclic
  group? If so, the k=4 search should target the same group family (Cayley over
  Z_a × Z_b, dihedral, etc.) — a space my circulant search does NOT cover.
