# E944 — Annealing assault results (count, ASSAULT MODE)

Recipe-A: scorer = exact #critical-edges, simulated annealing to drive it to 0.
Engine `critedge.py` / hunter `checkers.py`. Reproduce: count_anneal*.py.

Move-sets tried (escalating): (1) random add/del/2-swap; (2) reheat+restart,
dual seed; (3) targeted de-criticalization (3-color G−uv, add coloring-breaking
edge); (4) degree-preserving strict-6-regular; (5) min-deg-6 irregular; (6)
BASIN-HOPPING (count_basinhop.py) — large multi-swap jumps to escape proximity's
rigid n/3 plateau, then local re-settle, staying 6-regular. (6) is proximity's
exact-identified escape lever; running. NO witness in (1)-(5); the n/3 plateau is
robust under local moves (proximity: all 39 single-adds + all 416 2-swaps around
C13(1,2,5) stay pinned at 13 or exit the 4-vtx-critical class).

## Detection validated (so the negative is credible)
The scorer's witness-detection was validated on a REAL (5,1)-graph: jensen's
G_(5,2,2) = circulant on Z₁₇ with distances {1,3,4,5}. `score(g, want_chi=5)`
returns EXACTLY 0.0 with info (5,0,0). So a true (4,1)-witness, if any chain
reaches it, WILL register as score 0 — no false negatives in detection. This makes
the "no witness found" result meaningful rather than a possible detection failure.

## The scorer fix that unstuck the manifold
forge's hard-reject annealer got "stuck — manifold too rigid for local moves."
**Fix: SOFT scorer.** Evaluate score on ANY graph, penalize infeasibility:
`score = 50·χ_penalty + (8–12)·(#non-critical-vertices) + 1·(#critical-edges)`.
Chains cross infeasible regions (χ≠4 or not-vertex-critical) and re-enter feasibility
lower down. This works: chains move freely where hard-reject froze.

## Move-sets tried
1. Random add/delete/2-swap (count_anneal.py).
2. Reheat + restart, dual seed families (count_anneal2.py).
3. **Targeted de-criticalization** (count_anneal3.py): for a critical edge uv,
   3-color G−uv, add an edge between two same-colored non-adjacent vertices to
   break that coloring. Non-local — escapes proximity's circulant basin.
4. **Degree-preserving 6-regular** (count_anneal_6reg.py): ONLY 2-swaps, staying
   exactly 6-regular (Steiner Problem 5.2). [the decisive, feasible search]

## THE KEY CAVEAT (load-bearing — corrects an over-optimistic early read)
Unconstrained chains (moves 1–3) reached 9–10 critical edges at n=13 — BELOW the
circulant floor of 13 — which looked like progress. **But the E* fragmentation
diagnosis revealed these graphs achieve the low count by DROPPING below min-degree 6**
(score-9 graph had degree sequence [4,4,4,4,4,5,5,5,5,5,5,6,6], min-deg 4). By
Prop 5.1 (gallai/proximity, rigorous) a witness needs **min-deg ≥ 6**. So those
low-count graphs **can never be witnesses** — the annealer was escaping the
feasible region, not approaching a witness.

When CONSTRAINED to stay 6-regular (move-set 4, degree-preserving), the chain
plateaus at **13 critical edges at n=13** = exactly the circulant floor. The
6-regular manifold does NOT let critical count drop below ~n in our runs. [running
n=12–18 for the full per-n floor; results below as they land.]

## E* (critical-edge subgraph) structure — a genuine structural finding
For the (infeasible, min-deg<6) near-witnesses, E* FRAGMENTS as critical count drops:
| graph | n | #crit | E* spanning? | E* connected? | components | untouched verts |
|---|---|---|---|---|---|---|
| C₇(1,2)    | 7  | 7  | YES | YES | 1 | 0 |
| C₁₃(1,2,5) | 13 | 13 | YES | YES | 1 | 0 |
| C₁₆(1,2,5) | 16 | 16 | YES | YES | 1 | 0 |
| K₄         | 4  | 6  | YES | YES | 1 | 0 |
| anneal score-9 (min-deg 4!) | 13 | 9 | **NO (12/13)** | **NO (3 comps 5,5,2)** | 3 | 1 |

So: **all 6-regular/circulant graphs have E* connected+spanning** (matches
Jensen–Siggers conjecture). E* only fragments once we LEAVE the 6-regular class.
Reading: the J–S "E* connected/spanning" pattern appears tied to the high-density
(6-regular) regime. Whether a 6-regular graph can have fragmented/empty E* is the
open question — our degree-preserving search has not produced one (plateau at ~n).

## The 6-regular vertex-criticality obstruction (sharpening, n=12)
The degree-preserving 6-regular chain at n=12 is STUCK at info (χ=4, 4 non-critical
vertices, 6 critical edges) — it cannot even reach full vertex-criticality on the
6-regular manifold at n=12, let alone drive critical edges down. This matches:
- proximity: NO 6-regular graph on 11 vertices is 4-vertex-critical.
- hunter: n=11 δ≥6 → 0 four-vertex-critical graphs.
- The double-bind: 6-regular + 4-chromatic graphs tend to have REDUNDANT vertices
  (not vertex-critical). Where both hold (C₁₃(1,2,5), n=13), critical count is stuck ≈ n.
The min-deg-6 IRREGULAR chain (count_anneal_mindeg6.py) shows the same: at n=14 it
reduces non-critical vertices from 14→6 but can't reach 0 while staying min-deg-6.

This is the SHARP structural tension at the heart of E944, now seen from the
search side: the witness must be simultaneously DENSE (min-deg ≥ 6, forced by
Prop 5.1) and vertex-critical (which density fights), AND have no critical edge
(which the circulant near-misses show wants the difference-1 orbit alive). Three
conditions pulling against each other; annealing finds graphs satisfying any two.

## The interpolation experiment (clincher for "failure modes are tied")
Seeded annealing directly from C₁₄(1,2,5) — the graph that has ZERO critical edges
but all 14 vertices non-critical — with the soft scorer rewarding vertex-criticality.
Result: the chain DID repair vertex-criticality (non-critical vertices 14→0), but in
doing so it **recreated 12 critical edges AND dropped min-degree to 3** (deg-seq
[3,3,4,4,4,4,4,4,5,5,6,6,6,6]). So moving off the "0-critical-edge corner" toward
vertex-criticality immediately re-introduces critical edges and exits the feasible
(min-deg-6) region. **The two failure modes are dynamically TIED** — local moves
cannot interpolate between "vertex-critical with critical edges" and "no critical
edges but not vertex-critical." This is the search-side signature of the obstruction.

## Random-seed feasibility note (why circulant seeds matter)
On the 6-regular manifold, random 6-regular seeds at n=13 anneal to graphs stuck at
(χ=4, 6–7 non-critical vertices, ~5 critical edges) — they do NOT reach full vertex-
criticality. The known good graph C₁₃(1,2,5) is a RARE needle random annealing
seldom lands on. So even "find a 6-regular 4-vertex-critical graph at all" is hard
via local search at n=13; circulant seeds are what give a feasible start. This
compounds the difficulty of driving the critical count to 0.

## Basin-hopping verdict (proximity's escape lever — DOES NOT escape)
Tested basin-hopping from C₁₃(1,2,5): 15 large-step hops, each = k random
degree-preserving 2-swaps (k=3..9, unconditional jump) then a 2500-iter local
re-settle, staying 6-regular. RESULT: **every feasible landing has EXACTLY 13
critical edges; never below.** The non-feasible hops all land at (χ=4, 7 non-
critical vertices, 5 critical edges) — i.e. they break vertex-criticality. So even
LARGE-STEP jumps either return to the 13-plateau or fall out of the 4-vertex-
critical class. The n/3 critical-edge floor at n=13 is **robust under both local
AND large-step moves.** This directly answers proximity's open question: the
plateau is not a mere local-search artifact escapable by basin-hopping.

## Status / verdict
- No witness found across SIX strategies incl. basin-hopping. The honest signal:
  **on the feasible 6-regular manifold the critical-edge floor is ≈ n and is robust
  to local + large-step moves**; dropping it requires leaving min-deg-6, which
  disqualifies the graph as a witness. Mild IMPOSSIBILITY-leaning intel for the
  6-regular case (Steiner Problem 5.2), consistent with proximity's circulant basin
  trap at n/3, the squad's 0-witness floor (n≤11 exhaustive), and the mod-3 dichotomy.
- Caveat: annealing is heuristic; a negative is NOT a proof. A witness could be a
  6-regular graph our SA never reaches, or non-regular (min-deg 6 but irregular,
  m > 3n) which our degree-preserving search excludes by construction.
- NEXT if plateau holds: relax from strict 6-regular to "min-deg ≥ 6, irregular
  allowed" with a STRONG min-deg penalty (not the weak one that failed in anneal4),
  to cover the m > 3n feasible region.
