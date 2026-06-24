# E944 — Independent small-n ground truth (skeptic)

Duty #2: establish the small-n ground truth with MY OWN enumerator and TWO independent
χ-checkers that must agree, then cross-check against hunter's and count's independent
enumerations. ("Two independent enumerations or it didn't happen.")

Engine: `skeptic_enum.py`. Reproduce: `python3 skeptic_enum.py <Nmax> <Nmin> <mindeg>`.

## Independence design
- **Enumeration source:** nauty `geng -c` (exhaustive canonical, each iso class once).
  Distinct from count's `networkx.graph_atlas_g` (n≤7) and complementary to hunter's geng.
- **χ-checker A:** from-scratch recursive backtracking, greedy-clique lower bound,
  most-constrained-vertex ordering + new-color symmetry break. My own code (`chi_A`).
- **χ-checker B:** SAT k-colorability via python-sat / Cadical (`chi_B`).
- **Every** graph reaching the criticality test has χ computed by BOTH A and B; a mismatch
  ABORTS the run (`chi()` raises SystemExit). hunter SAT-checks only a sample; I SAT-check
  ALL — so my run is the stronger cross-validation of the χ values themselves.
- Self-test before sweeping: A and B agree with each other AND with the known χ of K4(4),
  K5(5), C5(3), C6(2), Petersen(3), Grötzsch(4), K3,3(2), W5(4), Moser spindle(4). All pass.

## Results — every 4-vertex-critical graph on ≤ n has a critical edge

| n | geng -c graphs | 4-vertex-critical | have critical edge | **WITNESS (no crit edge)** | χ cross-checks (A=B) | disagreements |
|---|---|---|---|---|---|---|
| 4 | 6 | 1 (K4) | 1 | 0 | ✓ | 0 |
| 5 | 21 | 0 | 0 | 0 | ✓ | 0 |
| 6 | 112 | 1 | 1 | 0 | ✓ | 0 |
| 7 | 853 | 7 | 7 | 0 | ✓ | 0 |
| 8 | 11,117 (full) / 2,589 (-d3) | 8 | 8 | 0 | 18,651 | 0 |
| 9 | 84,242 (-d3) | 124 | 124 | 0 | 157,905 | 0 |
| 10 | 5,203,110 (-d3) | (running; redundant verify of hunter's 2,453) | — | — | — | — |

n=4..7 cumulative χ cross-checks: 1,553, all agreeing.

## min-degree-3 filter is SOUND (validated, not assumed)
A 4-vertex-critical graph has δ(G) ≥ 3: if deg(v) ≤ 2 then a proper 3-coloring of G−v
(which exists since χ(G−v)=3 when v is critical) leaves a free color for v among the 3,
extending to a 3-coloring of G — contradicting χ(G)=4. So v with deg≤2 is never critical.
**Empirically validated:** at n=8, full enumeration (11,117 graphs, no filter) and `-d3`
(2,589 graphs) BOTH yield exactly 8 four-critical graphs. The filter loses nothing.

## CROSS-CHECK vs peers (the "two independent enumerations" requirement) — PASSED
Three mutually independent pipelines agree on the 4-vertex-critical counts:

| n | skeptic (geng; backtrack+SAT, ALL χ cross-checked) | hunter (geng; backtrack, SAT-sampled) | count (graph_atlas; DSATUR) |
|---|---|---|---|
| 4 | 1 | 1 | 1 |
| 5 | 0 | 0 | 0 |
| 6 | 1 | 1 | 1 |
| 7 | 7 | 7 | 7 |
| 8 | 8 | 8 | (atlas stops at 7) |
| 9 | 124 | 124 | — |
| 10 | (verifying) | 2,453 | — |

Independent agreement on all overlapping n. The counts also match the known small-4-critical
catalog (K4 at n=4; the unique n=6 graph = the odd-wheel/W5 relative; 7 graphs at n=7).

## GROUND TRUTH ESTABLISHED
> Every 4-vertex-critical graph on ≤ 9 vertices HAS a critical edge (skeptic, fully χ-cross-checked).
> ≤ 10 confirmed by hunter; my n=10 redundant verification in progress.
> Therefore any E944 witness (k=4, r=1) has **≥ 11 vertices**.

This is a verified LOWER BOUND on the witness size, not evidence the witness exists or not.
Consistent with TRUE (known k≥5 witnesses are larger graphs) and with FALSE. It only kills
tiny witnesses. By the statement-lock (skeptic_statement_lock.md), this finite ground truth
is exactly what the Lean statement reduces to — no infinite case escapes it.

## Files
- `skeptic_enum.py` — the enumerator + dual χ-checkers (self-test included).
- `skeptic_n9.log`, `skeptic_n10.log` — raw run logs.
