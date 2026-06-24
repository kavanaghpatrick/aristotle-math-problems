# E944 — JOINT experiment: WALL-5 descend + count pair-move cross (count + wall)

**Verification:** `python3 analysis/e944/team/wall5_pairmove.py`. Exact χ throughout.
WALL-5 reconstruction matches wall's reported numbers (Grötzsch 20→13; Myc(C7) 28→20,
wall reported 18 — same plateau-at-≈n structure, greedy-randomness variance).

## The experiment
wall's WALL-5 primitive: from a 4-vertex-critical Mycielskian seed, greedily ADD the
non-edge that most reduces #critical-edges while preserving vertex-criticality, until
plateau (≈ n+small). Then count's pair-move SA (acts on the critical-edge/non-critical-
vertex COUPLING, corner-seeking product+sum potential) tries to cross the last gap to
a genuine witness (0 critical edges AND vertex-critical).

The point: WALL-5 plateau graphs are (a) asymmetric (Mycielski-derived, NOT circulant —
a DIFFERENT basin), and (b) already much closer to the corner than the circulant near-
misses. If the pair-move can't cross even from there, the (0,0) corner is unreachable
across independent basins → strong combined impossibility intel.

## Result — pair-move does NOT cross, from EITHER seed
| seed | WALL-5 plateau | pair-move best reached |
|---|---|---|
| Grötzsch / Myc(C5), n=11 | critE=13, vertex-critical, min-deg 3 | (χ=4, **11 non-critical vertices**, 0 critical edges) |
| Myc(C7), n=15 | critE=20, vertex-critical, min-deg 3 | (χ=4, **14 non-critical vertices**, 0 critical edges) |

In BOTH cases the pair-move reaches 0 critical edges ONLY by pushing nearly ALL
vertices non-critical — it slides to the OVER-FULL corner (the n≡2 / "0 critical edge
but not vertex-critical" corner), never to the (0,0) witness. Exactly as CNT-7's blame
analysis predicted and as the circulant searches showed.

## Why this is a strong COMBINED result
Three INDEPENDENT basins now exhibit the identical wall:
1. **Circulant basin** (C₁₃(1,2,5)): basin-hopping + 416 swaps pinned at critE=n.
2. **Mycielski basin** (Grötzsch, Myc(C7)): WALL-5 descends to ≈n then plateaus; pair-
   move slides to the over-full corner.
3. **Random 6-regular** (wall, n=31): all non-vertex-critical (over-dense corner).
Every route to "0 critical edges" passes through losing vertex-criticality. The two
witness conditions (0 critical edges, vertex-critical) are realized on DISJOINT regions
of every basin searched — local + construction-side moves cannot reach their
intersection. This is the debt-trade / 3-way tension confirmed from construction
(WALL-5), local-move (pair-move), and coloring-incidence (CNT-7 blame) angles at once.

## Honest status
No witness. Heuristic search across three independent basins (circulant, Mycielski,
random) plus the WALL-5 construction primitive all bottom out at the same wall: the
(0,0) corner is not reachable by local trade-moves or greedy construction. This is a
mild-to-moderate IMPOSSIBILITY signal — stronger than any single-basin result because
it's basin-independent — but still heuristic, NOT a proof. A witness, if it exists,
sits in a region no descent path from these seeds reaches (asymmetric, non-Mycielski,
non-circulant, right at the chromatic threshold). The clean joint statement is the
deliverable; the actual resolution needs the structural/impossibility proof (wall L2,
gallai, or a min-conflict≥2 existence argument).
