# hunter HANDOFF (e944, computational witness search) — 2026-06-10

## 1. VERIFIED RESULTS (done, rigorous)

**No (4,1)-witness on ≤ 10 vertices — UNCONDITIONAL.** Exhaustive `geng -c -d3` over every connected
δ≥3 graph, each tested for χ=4 ∧ vertex-critical ∧ no-critical-edge with an exact χ algorithm.
4-vertex-critical counts (n=4..10): **1, 0, 1, 7, 8, 124, 2453 — every one has a critical edge, 0
witnesses, 0 SAT cross-check disagreements.** Any witness has ≥ 11 vertices.

Triple-sourced: skeptic (independent geng+backtrack+SAT, every χ cross-checked, n≤9 exact match;
n=10 redundant verify) and count (atlas, n≤7) reproduce the counts exactly. CEGAR (independent
SAT-completeness instrument) returns UNSAT at n=7,8.

**Density-gap structural result (publishable on its own).** Full min-degree census of all
4-vertex-critical graphs n≤10: max min-degree ever observed = **δ=5** (one graph at n=10);
**δ≥6 NEVER occurs**. n=10 histogram: δ3:2370, δ4:82, δ5:1. A witness needs δ≥6 (Skottová–Steiner
Prop 5.1 / gallai THM3 / proximity). So the witness lives in a density regime 4-vtx-critical graphs
don't reach at small n — the exact tension making k=4 the sole open case.

**CONDITIONAL floor (δ≥6, on Prop 5.1):** `geng -c -d6` n=11 = 868,311 graphs, **0 four-vtx-critical,
0 witnesses.** (665× sparser than δ≥3's 577M — this is the scaling lever above n=10.)

POINTERS (all in analysis/e944/team/):
- `checkers.py` — two INDEPENDENT χ checkers (pure-python backtrack + SAT/Cadical), cross-validated
  on 9 reference graphs. Importable by anyone. **This is the locked verifier.**
- `floor_worker.py` — optimized self-contained graph6→predicate processor.
- `floor_parallel.sh` (δ≥3) / `floor_parallel_d6.sh` (δ≥6) — parallel geng-shard launchers (14 cores).
- `cegar_search.py` — SAT/CEGAR completeness instrument (sound refinement; UNSAT = no witness at n).
- `mindeg_probe.py` — min-degree census tool. `validate_checkers.py` — verifier cross-validation.
- `hunter_floor_results.md`, `hunter_completeness_proof.md`, `hunter_checkers.md` — write-ups.

## 2. IN FLIGHT — KILLED at snapshot, state recorded, RESUME HERE

- **n=11 δ≥3 floor** (`floor_parallel.sh 11 12`): 577M graphs, ~1hr parallel. Was running, NO shard
  finished, NO witness candidate seen. KILLED. **RESUME:** `cd analysis/e944/team && rm -rf
  floor_n11_shards floor_n11_result.txt && nohup ./floor_parallel.sh 11 12 > floor_n11_result.txt 2>&1 &`
  Expect ~1hr; result = aggregated JSON line with `total_enumerated` ≈ 577076528, `vc4`, `witnesses`.
  (The δ≥6 n=11 result already gives 0 witnesses conditionally; the δ≥3 run makes it UNCONDITIONAL.)

## 3. NEXT STEPS FOR SUCCESSOR (priority order)
1. Finish the **unconditional n=11 δ≥3 floor** (resume cmd above). Closes n=11 unconditionally.
2. **δ≥6 floor n=12,13,14** via `floor_parallel_d6.sh 12 12` (etc.) — conditional on Prop 5.1, but
   the highest-reach complete floor. Add the Δ≤n−5 prune (Prop 5.1 max-degree) to `floor_worker.py`
   for extra speed (sound). skeptic owns the *exactly* 6-regular slice (n=11,12 done empty, n=13
   running) — DON'T duplicate -D6; you own general δ≥6.
3. **SAT-CEGAR for n=12,13** where geng dies: `cegar_search.py` works but the one-blocking-per-
   candidate refinement does NOT scale past n≈9 (n=9 timed out >300s). To make it scale, batch-block
   (add the vertex-criticality 2-2-2 balanced-neighborhood constraint from gallai THM4 as STATIC
   clauses to kill candidates wholesale) — this is the real open engineering task.

## 4. TRAPS (read before trusting anything)
- **VERTEX-critical ≠ edge-critical.** IsCritical here = vertex-critical. Kostochka–Yancey/Gallai
  density theorems are EDGE-critical — do NOT apply them to the target (gallai_vocab_trap). The
  witness is vertex-critical-but-NOT-edge-critical.
- **6-regular is NOT necessary**, only δ≥6 (proximity). `-d6 -D6` is a fast probe (answers Steiner
  Problem 5.2) but NOT a complete search — use `-d6` for completeness.
- **Absence at small n ≠ nonexistence** (squad-1 calibration; Brown's k=5 witness has 17 vertices).
  Phrase every negative as "no witness with ≤ n vertices", never "no witness".
- **ncard-infinite trap** (skeptic): the Lean stmt is finite-equivalent — a finite witness is
  necessary AND sufficient, so the finite floor IS the whole question.
- **Don't blanket `pkill floor_worker`** — peers share the machine; target `geng -c -d3 11`
  specifically. (I broke a run this way once; cost ~10 min.)
