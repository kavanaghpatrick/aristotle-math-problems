# proximity HANDOFF — E944 (Martinsson–Steiner lane)

## 0a. THE SQUAD SEARCH INSTRUMENT (canonical, team-lead-blessed) — `e944_search_instrument.py`
The ONE witness-search tool at n≥14, co-owned with hunter. Architecture (load-bearing, in the header):
the (4,1) property RESISTS LOCAL ENCODING (non-criticality is global) ⟹ GENERATE + GLOBAL-VERIFY,
NOT constrain-and-solve. Pieces: geng -c -d6 -D{n-5} generation + optional exact degree-profile pin +
res/mod sharding → SOUND prefilters (Prop-5.1 degree, 2-set-boundary≥6, full λ≥6) → incremental
verifier (CEGAR-free) → dual-check + skeptic_adjudicate on any 0-hit. Self-tested (rejects near-misses;
n=11 smoke = 0/266). Honest: prefilters add ~no pruning in the tight -d6 |E|=40 regime (geng -d6 already
implies them); value = unification + faster verify + degree-profile pinning + sound-by-construction.
RETIRE for compute focus: proximity_witness_sat.py bulk CEGAR (doesn't scale), any duplicate scanners.

## 0. INVENTION BLITZ — ENCODINGS lane (proximity), all in INVENTIONS.md + working code
12 candidate encodings over 4 rounds (6 validated, 2 dead-with-diagnosis, 4 designed). Working tools:
- `proximity_incremental_verifier.py` — CEGAR-FREE (4,1) verifier (ENC-2 vertex-deactivation + ENC-6
  edge-deactivation on ONE persistent solver). Self-tested vs checkers. DROP-IN for hunter's loop.
- `proximity_cegar_constraints.py` — gallai THM4 static prune (use degree_exactly_6=False for general
  search!) + λ≥6 2-set relaxation. Kills the has-critical-edge class pre-CEGAR.
- KEY data findings from the blitz: (a) low-critical graphs are LOW-symmetry + NON-regular (forge n=10
  champ |Aut|=4, degs [4^6,5^4]) → search asymmetric non-regular (ENC-7/8). (b) vertex-criticality is
  the BINDING SCARCITY at n=13 (even non-regular profile 6^11·7^2 sample: 0 vertex-critical) → push to
  n≥14 where the critical-vertex window opens (4/11→8/12 trend). (c) LOCAL moves are UNIVERSALLY
  plateau-trapped at the seed's critical-count (circulant: 39 adds+416 swaps+count basin-hop; forge
  champ: single-adds all pinned at 8) → need MULTI-EDGE moves or larger n. (d) Hajós-closure builds the
  WRONG object (edge-critical, all-edges-critical) — confirms gallai vocab trap from generator side.
- Best alive encodings to act on: ENC-1 (m*(G)≥2 ∧ m*(G−v)=0 witness criterion via min-mono-edges),
  ENC-5 (lex-leader + degree-profile pinning for n≥14), ENC-12 (front-load vertex-criticality since
  it's the scarce property). ENC-11 (multi-edge redundant growth) handed to count.

## 1. RESULTS (done, on disk)

**Papers fully read + extracted** (PDFs: `/tmp/ms2023.txt` = arXiv:2310.12891; `/tmp/ss2025.txt` =
arXiv:2508.08703 — re-download with `curl -sL arxiv.org/pdf/<id>` if /tmp cleared):
- `proximity_martinsson_steiner.md` — FULL extraction of BOTH Steiner papers + interpolation ladder
  + computational results. The 2023 M-S paper (probabilistic, hypergraph-complement) and the FRESH
  2025 follow-up **Skottová–Steiner arXiv:2508.08703** (resolves k≥5, leaves ONLY k=4 open).
- KEY literature facts: k=4 is the SOLE open case, confirmed open as of Aug 2025. Experts (Steiner)
  "lean towards NO" but **only for circulant graphs**, and that lean is EMPIRICAL ("couldn't find
  them"), NOT a theorem. No general impossibility, no competitor claiming resolution. Prior is
  genuinely uncertain.
- **Prop 5.1 (necessary conditions for any (4,1)-graph), verified, independently re-derived by
  skeptic from the coloring side:** min-deg ≥ 6, edge-connectivity ≥ 6, Δ ≤ |V|−5, |V| ≥ 11. NO
  |V| upper bound. 6-regular is the SPARSEST case (Steiner Problem 5.2), NOT a necessary condition.
- Gluing Lemma 2.1: one (4,1)-graph seed → infinitely many of all large orders (consumes a seed;
  useless for finding the first). Relayed to forge.

**Rung H — the M-S hypergraph route is PROVABLY EMPTY at k=4** (`proximity_rung_h.md` + `.py`):
- Route is rigid to the unique order **n=13** for (k=4, r=1).
- R1 (exact counting): property (i) forces |E(H)| ≥ 5; property (ii) fails at |F|=5 (need union ≥ 15
  > 13). M-S sufficient condition infeasible.
- R2 (degree, NEW): densest G the route outputs has min-deg ≤ 4 < 6 = Prop 5.1 floor. Independently
  re-derives Prop 5.1 from the hypergraph side.

**Rung 4 — Steiner Problem 5.2 (6-regular (4,1)-graph?) cleared at n=11, n=12** (`proximity_6regular.py`):
- n=11: 266 connected 6-regular graphs, **0 even 4-vertex-critical**, 0 witnesses.
- n=12: 7849 graphs, 0 vertex-critical, 0 witnesses.
- Near-miss trend: max #critical-vertices in a 6-regular χ=4 graph climbs 4/11 → 8/12 (window opens
  with n). All χ cross-checked backtrack vs SAT, 0 mismatches.

## 1b. ASSAULT-MODE RESULTS (post-snapshot; team-lead constraint-engineer order)
Files: `proximity_ladder.md` + `proximity_ladder.py` + `proximity_witness_sat.py`.
- **6-regular CIRCULANT route CLOSED** (no 6-reg circulant is a (4,1)-graph): every 6-reg
  vertex-critical circulant has critical-count > 0, NEVER 0. ROBUST through n=31 (my exhaustive sweep
  n≤21 + wall's n=31 spot-checks, dual-checked). Headline intact; witness must be non-circulant.
  ⚠ CORRECTION (wall, re-verified by me): my earlier "EXACTLY ONE critical orbit / fraction 1/3" was
  an n≤21 ARTIFACT — FALSE at n=31 (C31(1,4,6), C31(5,6,7) have TWO critical orbits, 2n edges, 2/3).
  DO NOT use a "one-orbit" theorem. Only the WEAKER "critical-count > 0" survives.
  FAMILY-SPECIFIC SURVIVOR: C_n(1,2,5) DOES stay single-diff-1-orbit (fraction 1/3) through n=31
  (verified n=13..31, n≡1 mod 3) — so the C_n(1,2,5) mod-3 dichotomy below is fine; only the
  ALL-connection-sets generalization was wrong. VERIFY any circulant structural claim to n≥31.
- **n=11 PROVABLY witness-free for the ENTIRE Prop-5.1 class** (at n=11, min-deg≥6 ∧ Δ≤6 force
  exactly-6-regular; 0 of 266 vertex-critical). Sharper than "6-regular cleared".
- **C13(1,2,5) is a RIGID PLATEAU**: all 39 single edge-additions lose vertex-criticality; all 416
  degree-preserving 2-swaps stay pinned at 13 critical edges. → told count's SA it needs non-local
  escape from the circulant basin (trapped at n/3).
- **Structural SAT model** (proximity_witness_sat.py): edge-vars + min-deg≥6, Δ≤n−5 (seq-counter
  cardinality), K4-free, edge-window + CEGAR + λ≥6 post-hoc. VALIDATED at n=11 |E|=33 (matches geng).
  CAVEAT: CEGAR throughput is too low to out-enumerate geng for BULK non-regular slices — use TARGETED
  only; bulk floor belongs to hunter's geng campaign.
- **SYNTHESIS with forge's exhaustive n≤10 profile**: forge's graph-wide min-critical DECREASES
  (n=8→12, 9→9, 10→8; fraction→64%) via NON-regular non-circulant graphs. Circulants are a rigid n/3
  sub-family OFF that trend. ⟹ a witness (if any) follows forge's non-regular trend into larger n;
  circulant + M-S routes are closed.
- **CONSTRAINT ENGINEERING for hunter's existence_cegar.py** (`proximity_cegar_constraints.py`,
  validated): three SOUND clause generators bolting onto hunter's e[]/cV[]/c4[] vars.
  - `thm4_apply(solver,pool,n,e,cV, degree_exactly_6=False)` — gallai THM4 forced 2-2-2 as STATIC
    clauses on the baked 3-colorings. VALIDATED: rejects C13(1,2,5) (vertex-critical w/ critical
    edges) → UNSAT, i.e. kills the whole "vertex-critical-but-has-critical-edges" class pre-CEGAR.
    SOUNDNESS BOUNDARY (critical): degree_exactly_6=True (exactly 2-2-2) is sound ONLY for an
    exactly-6-regular search; for general min-deg-6 (degrees up to n−5) use False (atleast-2 only) —
    a witness may have a deg-7 vertex with 3-2-2. The atleast-2 form STILL rejects C13(1,2,5).
  - `edge_connectivity_2set_clauses(...)` — λ≥6 sound relaxation: every 2-subset boundary ≥6
    (cardinality). Sound since |V|≥11. Still verify λ≥6 post-hoc (covers only small cuts).
  - Q2 advice: lazy vertex-criticality (drop baked cV, CEGAR it) for smaller per-iter instances; or
    keep baked + add THM4 (tighter propagation). Subset-of-vertices baking is NOT sound.

## 2. IN FLIGHT (none — all jobs finished or killed cleanly)
- n=13 exactly-6-regular scan (Steiner Problem 5.2) was killed incomplete at snapshot; n=11,12 done
  (0 witnesses). RESUME if wanted: `python3 proximity_6regular.py 13` (~10–12 min) — but note hunter's
  scaled -d6 campaign (n=14-20) and forge's annealer subsume this; not high priority.
- Slow n=13 structural-CEGAR run was killed (throughput too low vs geng). Do NOT rerun for bulk;
  the SAT model is for targeted/constrained sub-cases only.

## 3. NEXT STEPS for a successor
1. The witness search should concentrate on NON-circulant, NON-regular min-deg-6 graphs at n≥13,
   following forge's decreasing min-critical-fraction trend (the ONLY family showing progress toward
   0). Circulants (n≤19) and the M-S route are CLOSED — don't re-search them.
2. ARCHITECTURE that scales (settled with hunter 2026-06-10): monolithic witness-SAT SEARCH is a DEAD
   END at n≥13 (hunter's coloring-blocking CEGAR never converges; my generate-and-test blocks one graph
   per iter = too many graphs). The working stack = GENERATE with geng/annealer + CHECK each with
   hunter's bitmask floor_worker (FASTEST for scanning) + THM4 static
   prune to skip has-critical-edge graphs. My incremental verifier is CEGAR-free + blowup-free but
   SLOWER than floor_worker for scanning (0.36 vs 0.19ms at n=16) — its role is the INDEPENDENT 3rd
   VERIFICATION PATH in the candidate-adjudication gate, NOT throughput. hunter ABANDONED the scaled
   SAT-CEGAR; do not revive it.
   COMPLETE floor needs `geng -c -d6` (min-deg≥6, ANY max-deg ≤ n−5), NOT `-d6 -D6` (incomplete).
3. Help wall finish the circulant impossibility. NOTE the "exactly one critical orbit" claim is FALSE
   (n≤21 artifact; wall's C31(1,4,6)/C31(5,6,7) have TWO orbits). The SURVIVING statement is the
   weaker "no 6-reg circulant is a (4,1)-graph / critical-count > 0" (robust to n=31). The n-uniform
   proof of THAT is the gap; do NOT try to prove the one-orbit version.
4. Impossibility-side probe (interpolation ladder Rung 3): is #critical-edges ≥ const forced for ALL
   4-vertex-critical G? forge's profile (12→9→8) suggests NO (decreasing) — so the FALSE-answer route
   is weakening; lean is shifting toward "witness may exist at larger n / TRUE." Theorem 1.4 only
   upper-bounds the smallest critical SET, not the count.
5. The structural SAT model (proximity_witness_sat.py) is for TARGETED degree-sequence-pinned sub-cases
   only (NOT bulk search — see #2). The reusable pieces are the incremental verifier + THM4 prune.

## 4. TRAPS
- **gallai's vocab trap**: `IsCritical` = VERTEX-critical. Gallai/Kostochka–Yancey are EDGE-critical
  theorems — they apply to a DIFFERENT object. Don't import them onto the target directly.
- **skeptic's ncard-infinite trap**: a finite-edge witness is necessary AND sufficient; don't try to
  handle infinite V.
- **6-regular ≠ necessary**: only min-deg≥6 is. Exactly-6-regular searches are incomplete.
- **DB erdos_944 attempts are mirages** (per protocol). Compute for real; NEVER submit to Aristotle.
- The M-S 2023 result is LARGE-k by design (probabilistic threshold); its r=1 specialization does not
  even reach k=5. Don't expect to "tune it down" to k=4 — Rung H proves it can't.
