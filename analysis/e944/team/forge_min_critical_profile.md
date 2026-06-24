# E944 — Minimum-critical-edge profile by vertex count (forge)

**Question this answers:** How few critical edges can a 4-vertex-critical graph
have on n vertices? A witness (Erdős-944 k=4,r=1 object) exists iff this minimum
hits **0**. The profile tells us how the redundant-edge fraction grows with n,
which bounds how large any witness must be.

## Method (exact, reproducible)

- Enumerate ALL connected, min-degree-≥3 graphs on n vertices with `nauty geng`
  (`geng -c -d3 n  mine:maxe`, KY edge floor `(5n-2)/3`).
- For each, exact test: χ=4 (not 3-colorable, is 4-colorable), vertex-critical
  (every G−v is 3-colorable), then count critical edges (G−e is 3-colorable).
- All chromatic tests are exact backtracking k-colorability. Cross-checked
  against networkx on known graphs (K4, C5, Grötzsch, Petersen) in
  `forge_verify.py` self-tests.
- Scripts: `forge_sweep_min_critical.py`, `forge_7vertex.py`.

## Results

| n | #4-vertex-critical graphs | min #critical edges | m at min | redundant | % redundant | g6 of best |
|---|---|---|---|---|---|---|
| 4 | (K4) | 6 | 6 | 0 | 0% | — |
| 7 | 7 | **7** | 14 | 7 | 50% | `FUzro` = C7(2,3) = complement(C7) |
| 8 | 8 | 12 | 15 | 3 | 20% | `GCrdrk` |
| 9 | 124 | 9 | 19 | 10 | 53% | `HCp`fzy` |
| 10 | 2453 | **8** | 22 | 14 | **64%** | `ICpdbY{]_` |

**Headline:** No Erdős-944 witness exists on **n ≤ 10** vertices (exhaustively
verified — every 4-vertex-critical graph on ≤10 vertices has ≥8 critical edges).

**Trend:** Past n=8 the minimum critical-edge COUNT is decreasing (12 → 9 → 8)
while m grows, so the redundant FRACTION is climbing (20% → 53% → 64%). This is
consistent with — though does not prove — a witness existing at larger n.

## Key structural object: complement(C7) = circulant C7(2,3)

- Unique n=7 extremal graph. 4-regular, vertex-transitive (Z7 acts).
- Exactly 7 of 14 edges redundant; by vertex-transitivity the two edge-orbits
  (length-2 and length-3 chords) split into one critical orbit + one redundant
  orbit. This is the cleanest "parallel obstruction" example: removing a
  redundant-orbit edge leaves an odd-structure that still forces χ=4.
- Circulant route (see `forge_circulants.py`): for a circulant, vertex-
  criticality is all-or-nothing (transitivity) and edges of equal length are
  critical/redundant together. A witness circulant needs EVERY connection length
  to be a redundant orbit — only |S| conditions instead of m. This is the most
  promising scalable lever I have.

## Open / next

- n=11,12,13 are beyond naive geng (5.2M at n=10; ~10x per step). Handing the
  ≥11 floor to hunter (SAT/CEGAR). I continue on structured circulants and
  Hajós/Ore compositions that scale without exhaustive search.
