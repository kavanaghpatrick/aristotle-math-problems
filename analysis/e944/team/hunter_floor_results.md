# hunter — Exhaustive Floor Results for e944 (k=4, r=1)

## Result so far: NO WITNESS with ≤ 10 vertices.

Every connected min-degree-3 graph on n ≤ 10 vertices was enumerated by nauty `geng -c -d3`,
filtered to 4-vertex-critical, and tested for the no-critical-edge predicate.

| n | graphs enumerated (geng -c -d3) | 4-vertex-critical | with a critical edge | **witnesses (no critical edge)** | SAT disagreements | sec |
|---|---|---|---|---|---|---|
| 4 | 1 | 1 (K4) | 1 | 0 | 0 | 0.0 |
| 5 | 3 | 0 | 0 | 0 | 0 | 0.0 |
| 6 | 19 | 1 (W5) | 1 | 0 | 0 | 0.0 |
| 7 | 150 | 7 | 7 | 0 | 0 | 0.0 |
| 8 | 2,589 | 8 | 8 | 0 | 0 | 0.1 |
| 9 | 84,242 | 124 | 124 | 0 | 0 | 4.0 |
| 10 | 5,203,110 | 2,453 | 2,453 | 0 | 0 | 280.4 |

**VERIFIED LOWER BOUND: every 4-vertex-critical graph on ≤ 10 vertices has a critical edge.**
(So any witness to `erdos_944.dirac_conjecture.k_eq_four` has **≥ 11 vertices**.)

## Why min-degree-3 loses no witnesses (completeness argument)

A vertex `v` with `deg(v) ≤ 2` in a 4-chromatic graph G is NEVER critical: any proper 3-coloring
of `G − v` extends to `v` (≤ 2 forbidden colors out of 3), so `χ(G − v) = χ(G) = 4`, i.e. `v` is
not critical and G is not vertex-critical. Hence every 4-vertex-critical graph has `δ(G) ≥ 3`, and
`geng -d3` enumerates a SUPERSET of all candidates. nauty enumerates each isomorphism class exactly
once, so the floor is complete.

## Rigor / validation
- Primary χ: pure-python backtracking (`is_k_colorable_backtrack`).
- Every 4-vertex-critical graph that has a critical edge: a random sample (≤50/n) was re-verified
  with the INDEPENDENT SAT checker (Cadical). **Zero disagreements** across all n.
- Counts at n=4 (K4), n=6 (W5), n=7 (7 graphs) match the known catalog of small 4-critical graphs.

## Independent confirmations (cross-squad)
- **skeptic** ran an independent enumerator (geng + backtrack AND SAT, every χ cross-checked) and
  reproduced n=4..9 = 1,0,1,7,8,124 EXACTLY, plus validated the δ≥3 filter at n=8 (full 11117
  graphs vs -d3's 2589 → same 8 vertex-critical graphs). Independent enumeration #2.
- **count** atlas-confirmed n≤7. Independent enumeration #3.
- **CEGAR** (cegar_search.py): a SAT/CEGAR encoding (vertex-criticality + 4-colorability baked in;
  non-3-colorability and no-critical-edge enforced by SOUND lazy refinement clauses) returns UNSAT
  at n=7 (348 iters) and n=8 (1565 iters) — an independent COMPLETENESS instrument agreeing with
  the floor. (Does not scale past n≈9: one-blocking-per-candidate, n=9 timed out >300s.)

## STRUCTURAL FINDING — the density gap (why k=4 is hard, made quantitative)
4-vertex-critical graphs are SPARSE, but a (4,1)-witness must be DENSE. Min-degree distribution of
ALL 4-vertex-critical graphs (complete census):

| n | # 4-vtx-critical | min-degree histogram |
|---|---|---|
| 7 | 7 | δ=3: 6, δ=4: 1 |
| 8 | 8 | δ=3: 8 |
| 9 | 124 | δ=3: 123, δ=4: 1 |
| 10 | 2453 | δ=3: 2370, δ=4: 82, δ=5: 1, **δ≥6: 0** |
| 11 | (δ≥6 subset = 0) | **NO 4-vtx-critical graph with δ≥6 exists at n=11** |

Across the ENTIRE census n≤10 (complete), the maximum min-degree of any 4-vertex-critical graph is
**δ=5** (a single graph at n=10); δ≥6 never occurs. A witness needs δ≥6, so it lives in a density
regime 4-vertex-critical graphs essentially never reach until n is large.

By Skottová–Steiner Prop 5.1 (independently re-proven elementarily by **gallai**, THM 3; and
re-derived from the hypergraph side by **proximity**), any (4,1)-witness has **δ ≥ 6**. But the
census shows 4-vertex-critical graphs cap out at δ=4 through n≤9, and there are ZERO δ≥6
4-vertex-critical graphs at n=11. The witness lives in a regime (δ≥6, |V|≥11) that 4-vertex-critical
graphs essentially never reach at small n — this is the exact tension that makes k=4 the sole open
case. (Contrast k≥5: Brown's (5,1)-graph has δ=8, gallai verified; the dense vertex-critical regime
is reachable for larger k.)

## Two floors going forward
- **UNCONDITIONAL floor** (geng -c -d3, δ≥3 = proven-necessary): n≤10 done, n=11 running.
- **CONDITIONAL floor** (geng -c -d6, conditional on Prop 5.1 δ≥6): n=11 done = 0 witnesses
  (868,311 graphs, 0 four-vtx-critical). δ≥6 is 665× sparser than δ≥3, so this floor reaches much
  higher n. Pushing to n=12,13,14 once the δ≥3 n=11 run frees cores. If the witness is forced
  6-REGULAR (Steiner Problem 5.2), geng -d6 -D6 reaches n≈20+.

## NOTE on vertex-critical vs edge-critical
At n ≤ 10, every 4-VERTEX-critical graph found is also edge-critical (has a critical edge). The
witness, if it exists, is a vertex-critical graph that is NOT edge-critical — a rarer object. The
known constructions (Brown k=5, Jensen, Lattanzio) all build exactly such graphs for k ≥ 5.

## Files
- `checkers.py` — validated independent χ checkers (backtrack + SAT). Importable by any squad member.
- `floor_worker.py` — optimized single-shard graph6 processor (self-contained parser + predicate).
- `floor_parallel.sh` / `floor_parallel_d6.sh` — parallel geng-shard launchers (δ≥3 / δ≥6).
- `cegar_search.py` — SAT/CEGAR completeness instrument (independent of geng).
- `mindeg_probe.py` — min-degree census of 4-vertex-critical graphs.
- `validate_checkers.py` — cross-validation harness (9 reference graphs).
