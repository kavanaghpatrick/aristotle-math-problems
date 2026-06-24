# forge HANDOFF (snapshot 2026-06-10)

Role: constructive toolbox. Goal: build a 4-vertex-critical graph with NO critical
edge (Erdős-944 k=4,r=1 witness), or push the critical-edge fraction below
Jensen–Siggers.

## 1. RESULTS + FILE POINTERS

- **Verification harness** (exact χ, vertex-crit, critical-edge — backtracking
  k-colorability, self-tested vs K4/C5/Grötzsch/Petersen): `forge_verify.py`.
  Use `is_e944_witness(G)`. skeptic will independently re-verify any candidate.
- **Exhaustive min-critical-edge profile** (`forge_min_critical_profile.md`,
  `forge_sweep_min_critical.py`, `forge_7vertex.py`): exact min #critical-edges
  over ALL 4-vertex-critical graphs, via nauty `geng -c -d3` + exact χ:
  - n=7: 7 graphs, min 7 (g6 `FUzro`=C7(2,3), 50% redundant)
  - n=8: 8 graphs, min 12 (g6 `GCrdrk`)
  - n=9: 124 graphs, min 9 (g6 `HCp\`fzy`)
  - n=10: 2453 graphs, min **8** (g6 `ICpdbY{]_`, m=22, 14 redundant=64%, |Aut|=4, irregular)
  → **No witness n≤10.** Min critical FRACTION 1.0→0.5→0.80→0.47→0.36, trending
  down. Confirms hunter/skeptic floor; adds the finer min-count statistic.
- **Circulant route DEAD + why** (`forge_circulant_findings.md`,
  `forge_circulants.py`): swept C_n(S) |S|≤5, n≤40, exact. Always **exactly one**
  critical edge-orbit, never 0 (690 near-misses, 0 witnesses). Conjecture:
  vertex-transitive 4-chromatic ⇒ has a critical edge. Matches count/algebra
  (Cayley double-bind). **Witness is asymmetric.**
- **Literature** (`forge_literature_k4.md`): SkSt25 (arXiv:2508.08703) solved all
  k≥5,r≥1 ⟹ **k=4 is the SOLE open case**, even f_4(n)→∞ open. (Corroborated by
  archivist; he flags the better lever is Jensen–Siggers 2012, not SkSt circulants.)
- **CORE TENSION quantified** (`forge_double_cover.py`): biwheel (two apexes over
  an odd cycle, asymmetric) and two-wheels-shared-rim EASILY reach **0 critical
  edges (100% redundant)** — e.g. `biwheel(C7)` dropping apex-edges (a,0),(b,1):
  n=9 m=20 χ=4, 0 critical edges — BUT **not vertex-critical** (7 removable
  vertices). Edge-redundancy (fat graph) and vertex-criticality (lean graph) pull
  in OPPOSITE directions. This is the whole problem in miniature.

## 2. SEARCHES IN FLIGHT — all killed for snapshot, state noted

- `forge_anneal.py`, `forge_directed_growth.py`: simulated annealing & directed
  gadget-growth on the 4-vertex-critical manifold — **both STUCK at the seed's
  critical count** (round 0). The manifold is rigid: nearly every local move
  breaks vertex-criticality or pushes χ→5. Local incremental search does NOT work.
- `forge_overlay.py`: union of 2 edge-disjoint 4-critical graphs — fails (n≤9 has
  no room: 2×19 edges > C(9,2); and union isn't vertex-critical anyway). Killed.
- `forge_trim_to_vc.py`: was about to BFS-trim the 100%-redundant biwheels down to
  vertex-critical, measuring how many critical edges reappear. **Did not finish.**
  This is the most promising unfinished thread — see next steps.

## 3. NEXT STEPS (priority order)

1. **Finish the trim experiment** (`forge_trim_to_vc.py`): take the 0-critical-edge
   biwheels and trim removable vertices toward vertex-critical; the min critical
   count at the vertex-critical boundary is the real target. If any trim path hits
   vertex-critical with 0 critical edges → WITNESS.
2. **Jensen–Siggers gadget attack** (team-lead's main line; `archivist_jensen_siggers_2012.md`):
   reconstruct K_{2m,2m,2m} core (0 critical edges, rigid 3-coloring) + Θ(n)
   disagreement gadget G(m) holding ALL critical edges. Replace G(m) with asymmetric
   overlays so its edges gain redundant obstructions. Verify with `forge_verify.py`.
3. **Use wall's SHARP local prune** (validated): witness ⟺ for every v and every
   3-coloring of G−v, each color appears ≥2× in N(v). Implement as the search
   acceptance test — far cheaper than global edge sweep, and directly targets the
   color-BALANCE that circulants fail.
4. **Honor the hard constraints** (proximity/algebra, SkSt Prop 5.1): δ≥6, edge-
   connectivity≥6, n≥11, maxdeg≤n−5; sparsest = 6-regular. Pre-filter candidates;
   anything with a degree-5 vertex or 5-edge-cut is auto-rejected. Target 6-regular
   on 11–14 vertices (SkSt open Problem 5.2).

## 4. TRAPS

- **"0 critical edges" alone is meaningless** — the fat biwheels have it but aren't
  vertex-critical. BOTH conditions must hold simultaneously. Always run full
  `is_e944_witness` (χ=4 AND vertex-critical AND 0 critical edges).
- **ncard infinite trap** (skeptic): witness must be FINITE; that's already
  guaranteed by building Fintype graphs — no action needed, just don't claim an
  infinite construction.
- **geng edge-range syntax**: pass `mine:maxe` (both bounds). A lone `k:` makes
  geng treat k oddly (cost me a wrong n=8 run). Fixed in `forge_sweep_min_critical.py`.
- **Buffering**: never pipe a long background run through `| tail` (tail buffers
  to EOF). Write directly to a file with `python3 -u ... > log`.
- **Don't chase symmetry** (circulant/Cayley): proven dead by 3 of us independently.
- **Mycielski route fails** (wall): Grötzsch is vertex-critical but all edges
  critical. Verified.
