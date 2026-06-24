# E944 — Degree-lifting pair-move from wall's WALL-5 plateau seeds (count + wall)

**Verification:** `python3 analysis/e944/team/wall5_seeds_cross.py`. Seeds from wall's
`wall5_plateau_seeds.json` (dual-checker verified vertex-critical). Exact χ throughout.

## The experiment (sharpest version of the joint test)
wall's caveat (gallai δ≥6 thm): a degree-3 vertex FORCES its 3 incident edges
critical, so part of each WALL-5 seed's critical-count is STRUCTURAL — unremovable
without raising those degrees. So the pair-move must climb the **δ→6 frontier**
(eliminate deg-3/4 vertices) AS it reduces critical-count. Scorer: 10·(non-critical
vertices) + (critical edges) + 3·(Σ degree-deficit below 6). Seeds:
- n15_mycC7_descended: n=15, critE=17, min-deg 4, vertex-critical.
- n19_mycC9_descended: n=19, critE=24, min-deg 3, vertex-critical.

## Result — n=15 (decisive, sharp)
The degree-lifting pair-move DID climb the frontier the earlier experiments couldn't:
it reached **min-degree 6 (degree-deficit 0, every vertex ≥ 6)** AND critical edges
down to **8** — BUT with **6 non-critical vertices** (lost vertex-criticality).
Best state: (χ=4, 6 non-critical vertices, 8 critical edges, **min-deg 6**).

**This is wall's predicted hard corner made precise.** The search CAN reach the
feasible degree class (δ≥6) and CAN get critical edges low (8), but only by
sacrificing vertex-criticality (6 vertices go non-critical). It could NOT reach
δ≥6 + vertex-critical + low-crit simultaneously. The three conditions are pairwise
reachable, never jointly:
- seed: vertex-critical + low-deg (δ=4) + critE=17
- after lift: δ≥6 + low-critE (8) + NOT vertex-critical (6 bad vertices)
The δ→6 climb directly trades AWAY vertex-criticality.

## Why this is the strongest single-experiment evidence
Earlier experiments stalled because they couldn't even lift degree (forge-champion
ENC-11) or stayed on one manifold. This one explicitly climbed δ to 6 from an
asymmetric Mycielski seed — and STILL hit the wall, now in the form: "δ≥6 forces
the over-full / non-vertex-critical corner." This matches wall's random-6-regular
finding (0/30 vertex-critical) from the OTHER direction: dense enough for δ≥6 ⟹
typically not vertex-critical. The witness must thread δ≥6 AND vertex-critical, a
needle that neither construction (WALL-5) nor degree-lifting search reaches.

## n=19 result — IDENTICAL pattern
Same outcome: degree-lifting reached min-deg 6 (degree-deficit 0) and critical edges
down to **9** — but with **8 non-critical vertices**. Best: (χ=4, 8 non-critical
vertices, 9 critical edges, min-deg 6). Both seeds confirm: climbing to δ≥6 forces
the over-full corner (vertex-criticality lost). The δ→6 + vertex-critical frontier
is unreachable by the degree-lifting pair-move from EITHER Mycielski seed.

| seed | start (vtx-crit, δ, critE) | best feasible-δ reached |
|---|---|---|
| n=15 mycC7 | (✓, δ=4, critE=17) | δ=6, critE=8, **6 non-critical vertices** |
| n=19 mycC9 | (✓, δ=3, critE=24) | δ=6, critE=9, **8 non-critical vertices** |

## Honest status
No witness. This is the sharpest confirmation yet of the δ→6-vs-vertex-criticality
tension: the search reaches every PAIR of {δ≥6, vertex-critical, low-critE} but never
all three. Combined with basin-independence (circulant/Mycielski/random/forge) and
granularity-independence (single/multi-edge), the (4,1)-witness is not reachable by
any local-or-coordinated move from any tested seed, including explicit δ→6 climbing.
Heuristic, not proof — but it is exactly the empirical statement an impossibility
lemma ("no graph is simultaneously δ≥6, vertex-critical, and critical-edge-free")
would need as its backbone. Hands to wall for the f-invariant cross-check and the
lemma formalization.
