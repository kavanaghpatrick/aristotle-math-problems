# E944 — Complete census of 4-vertex-critical graphs, n=4..7 (count)

**Method:** exhaustive enumeration over ALL isomorphism classes of graphs on n
vertices via `networkx.graph_atlas_g` (complete for n≤7), exact chromatic number
by DSATUR branch-and-bound cross-checked against independent brute-force coloring
(self-test: 40 random graphs + named graphs all pass). Critical edge e := χ(G−e)<χ(G).
Reproduce: `python3 analysis/e944/team/enumerate.py`. Engine: `critedge.py`.

## Result: critical-edge histogram over ALL 4-vertex-critical graphs

| n | # 4-vtx-critical graphs (iso) | edge count m | min #critical-edges | histogram of #critical-edges |
|---|---|---|---|---|
| 4 | 1 (= K4)        | 6  | 6  | {6:1} |
| 5 | 0               | –  | –  | (none exist) |
| 6 | 1              | 10 | 10 | {10:1} |
| 7 | 7              | 11..14 | **7** | {7:1, 9:2, 10:1, 11:2, 12:1} |

**Zero E944 witnesses exist for n ≤ 7.** Every 4-vertex-critical graph on ≤7
vertices has ≥ 7 critical edges. The minimum #critical-edges does NOT decrease
toward 0 as n grows from 4→7; it stays ≥ 6, dipping to 7 at n=7 (where one graph
has exactly half its 14 edges critical).

## Structural facts confirmed
- **n=5 gap:** there is NO 4-vertex-critical graph on 5 vertices. (Consistent
  with theory: a 4-chromatic vertex-critical graph on 5 vertices would need χ=4
  with every vertex critical; the only 4-chromatic graphs on 5 vertices are K4
  plus an isolated/pendant structure which fails vertex-criticality, or wheels
  W5=K1+C4 which is 3-chromatic. K5 is 5-chromatic.)
- The unique n=6 graph (10 edges, all... no: 10 critical edges out of how many?
  m=10, all 10 critical) is **4-edge-critical** — it is the well-known graph
  W5-type / the n=6 4-critical graph (likely the "Moser/odd-wheel" relative).
- The n=7 graph with **7 critical edges out of 14** is the most informative
  approximate witness: 7 of its edges are NON-critical. Studying which 7 edges
  are non-critical (and what they have in common) is the best small-n signal for
  what a true witness would need to do globally. See count_approx_witness.md.

## Why min #critical-edges large is bad news for FALSE-via-counting, neutral for TRUE
A naive "minimum #critical-edges grows ⇒ never hits 0 ⇒ FALSE" argument FAILS,
because the known k≥5 witnesses (Brown, Jensen) DO hit 0 — vertex-critical with
no critical edge exists for k=5. So the count CAN be driven to 0 by the right
global construction; small-n exhaustion just shows the smallest such k=4 graph
(if any) is larger than 7 vertices. This is fully consistent with TRUE; it only
rules out tiny witnesses. The Brown k=5 witness has n=... (see archivist) — the
k=4 witness, if it exists, is plausibly of similar or larger order.

## Next
- Extend census to n=8,9,10 (atlas stops at 7; need targeted/random search or
  hunter's nauty catalog).
- Dissect the n=7 7-critical-edge graph: locate the 7 non-critical edges.
