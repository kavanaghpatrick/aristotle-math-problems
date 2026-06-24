# Interpolation ladder + constraint-engineered search — results (proximity, ASSAULT MODE)

Goal (team-lead): at n=13..16, find the MINIMUM critical-edge count over 4-vertex-critical graphs
satisfying Prop 5.1. 0 ⟹ witness; provable floor > 0 ⟹ impossibility intel.

Code: `proximity_witness_sat.py` (structural-SAT + CEGAR), `proximity_ladder.py` (min-critical-edge
optimizer). All χ cross-checked backtracking vs SAT via `checkers.py` (0 mismatches).

## RESULT 1 — n=11 is PROVABLY witness-free for the ENTIRE Prop-5.1 class (not just 6-regular)

At n=11, Prop 5.1 forces min-degree ≥ 6 AND max-degree ≤ n−5 = 6 simultaneously ⟹ **every
Prop-5.1-feasible graph on 11 vertices is exactly 6-regular**. My exhaustive geng scan already
showed 0 of the 266 connected 6-regular graphs on 11 vertices is even 4-vertex-critical. The SAT
model confirms: 0 vertex-critical graphs in the class ⟹ minimum critical-edge count = ∞ (no
4-vertex-critical graph exists in the feasible class). So **n=11 cannot host a witness — closed,
exhaustively, for the whole feasible class.** (This is sharper than "6-regular cleared": at n=11
the feasible class IS 6-regular.)

## RESULT 2 — the C_n(1,2,5) champion sits on a RIGID PLATEAU at critical-count = (diff-1 orbit)

Both genuinely-6-regular vertex-critical circulants behave identically:
- **C13(1,2,5):** 6-regular, χ=4, vertex-critical, **13 critical edges** = exactly the difference-1
  orbit (verified). Critical fraction 13/39 = 1/3.
- **C16(1,2,5):** 6-regular, χ=4, vertex-critical, **16 critical edges** = exactly the difference-1
  orbit. Fraction 16/48 = 1/3.

This is wall's mod-3 rigidity mechanism realized: {1,2}⊆S ⟹ the difference-1 edges are forced
critical. EXACT local search around C13(1,2,5):
- **All 39 single edge-additions LOSE vertex-criticality** (χ stays 4, but a vertex becomes
  non-critical). 0/39 stay in the 4-vertex-critical class.
- **All 416 degree-preserving 2-swaps:** only 13 stay 4-vertex-critical-6-regular, and EVERY ONE
  still has exactly 13 critical edges. None improves below 13.

⟹ C13(1,2,5) is on a **rigid plateau**: its entire 1-edge-addition + degree-preserving-swap
neighborhood either exits the 4-vertex-critical class or stays pinned at 13 critical edges. The
diff-1 orbit's criticality cannot be reduced by local moves. This is impossibility intel for the
"perturb a circulant" route — corroborates wall's theorem direction and tells count's annealer that
the circulant basin is a hard local trap at critical-count = n/3 (the SA scorer needs a non-local
escape, e.g. abandoning the circulant structure entirely / large-step moves to a different basin).

## RESULT 3 — the constraint-engineered SAT model (delivered, validated)

`proximity_witness_sat.py` encodes the Prop-5.1 necessary conditions as a SAT model over edge
variables:
- min-degree ≥ 6, max-degree ≤ n−5 (sequential-counter cardinality)
- edge-count window (for the regularity sweep)
- K4-freeness (sound prune for n ≥ 11)
- edge-connectivity ≥ 6 verified post-hoc (networkx; global cut constraints don't SAT-encode well)
- CEGAR loop: each structural solution fully verified for the (4,1) property; failures blocked.

Validated against ground truth: at n=11 |E|=33 (6-regular), 300 structural candidates → 275 χ=4,
**0 vertex-critical** (matches the exhaustive geng result exactly), 300/300 λ≥6.

LIMITATION found in practice: vertex-criticality is a coloring meta-property not directly SAT-
encodable, so the raw CEGAR enumeration finds non-vertex-critical structural candidates first and is
inefficient at reaching the rare vertex-critical region by blind enumeration. The productive mode is
SEEDED exact local search (Result 2) + handing the structural SAT to hunter as a complement to geng
for the regime where geng is too large. For driving the critical-count minimum DOWN, the live lever
is a non-local construction (forge) or count's SA with large-step escapes — local circulant
perturbation is plateau-trapped.

## RESULT 4 — 6-regular circulant sweep: NO circulant witness (robust), but the "one-orbit" mechanism is FALSE beyond n≤21

I swept ALL 6-regular circulants C_n(a,b,c) (every connection set, n=13..21) for vertex-criticality
and minimum critical-edge count (each χ + vertex-criticality + critical-count exact, dual-checked).

- **Only n ≡ 1 (mod 3) admit any 6-regular vertex-critical circulant in n≤21.** n=13: 6 connection
  sets; n=16: 4; n=19: 27. n=14,15,17,18,20,21: ZERO.
- **No 6-regular circulant is a (4,1)-graph** — every 6-reg vertex-critical circulant has
  critical-count > 0. THIS IS THE ROBUST RESULT and it survives to n=31 (see correction below).

### ⚠ CORRECTION (wall, 2026-06-10; I independently re-verified with checkers) — DO NOT use "one orbit"
My earlier claim "critical-count EXACTLY n = one full difference-orbit, fraction always 1/3" is
**FALSE — an n≤21 small-n artifact.** At n=31 there are 6-regular vertex-critical circulants with TWO
fully-critical orbits:
- **C31(1,4,6):** χ=4, 6-regular, vertex-critical, critical orbits = {diff-4, diff-6}, **62 = 2n**
  critical edges, fraction **2/3** (NOT 1/3). diff-1 non-critical.
- **C31(5,6,7):** χ=4, 6-regular, vertex-critical, critical orbits = {diff-5, diff-7}, 62 edges, 2/3.
Same small-n trap that broke wall's own uniqueness lemma (held to n≤27, failed at n=31); my sweep
stopping at n≤21 was inside the artifact regime. The "exactly one orbit / fraction 1/3 / orbit
relocates" STORY is wrong; the critical set can be 1 OR 2 orbits. There is NO clean one-orbit theorem.

**WHAT SURVIVES:** *no 6-regular circulant is a (4,1)-graph*, empirically confirmed through n=31
(every 6-reg vertex-critical circulant has critical-count ≥ 1 > 0 — n=13/16/19 → n; n=31 examples
→ 2n; wall confirmed 120 four-vc circulants at n=31, all critical-count ≥ 1). The witness must be
non-circulant — that headline holds. Only the WHY (orbit-count mechanism) is more complex than I said.
Any further structural claim about circulants MUST be verified to n≥31 (the artifact boundary).

### RESULT 4b — complete THREE-WAY mod-3 dichotomy for the flagship family C_n(1,2,5)

Combining my orbit-sweep with count's dichotomy (count_mod3_dichotomy.md). NOTE: this is the
SPECIFIC family C_n(1,2,5), NOT all circulants — and for THIS family the one-orbit/fraction-1/3
pattern DOES hold robustly: I verified C_n(1,2,5) at n=13,16,19,22,25,28,31 (all n≡1 mod 3) and the
critical set is the single diff-1 orbit (n edges, fraction 1/3) every time, through n=31. The
two-orbit artifact in the Result-4 correction is for OTHER connection sets (C31(1,4,6) etc.), not
for C_n(1,2,5). So the dichotomy below is family-specific and verified to n=31:
| n mod 3 | χ | vertex-critical? | #critical edges | fails which witness half |
|---------|---|------------------|-----------------|--------------------------|
| 0 (15,18,…) | 3 | — | — | not even 4-chromatic |
| 1 (13,…,31) | 4 | YES | n (single diff-1 orbit) | no-critical-edge |
| 2 (14,17,…) | 4 | NO  | 0               | vertex-criticality |

C_n(1,2,5) hits a DIFFERENT obstruction in every residue class. The two witness conditions
(vertex-criticality and no-critical-edge) live in MUTUALLY EXCLUSIVE residues — n≡1 gives the first,
n≡2 gives the second, n≡0 gives neither — so the family can NEVER satisfy both. Closed-form
impossibility for the flagship near-miss family; explains why tuning n cannot push it to a witness,
and why "remove the critical orbit" (drifting n≡1→n≡2) just trades one failure for the other.

## SYNTHESIS with forge's exhaustive min-critical profile (n ≤ 10)

forge's complete geng profile (forge_min_critical_profile.md) gives the GRAPH-WIDE minimum
critical-edge count: n=8→12, n=9→9, n=10→8 (redundant fraction climbing 20%→53%→64%). That
decreasing-count / rising-fraction trend is driven by NON-regular, NON-circulant graphs (forge's
n=10 champion ICpdbY{]_ is not 6-regular). My circulant law (every 6-reg vertex-critical circulant
pinned at critical-count = n, one orbit) is CONSISTENT: circulants don't follow the decreasing
trend — they're a rigid sub-family stuck at n/3. So the encouraging "min → fewer critical edges as n
grows" signal lives entirely OUTSIDE the circulant/regular families. A witness, if it exists, follows
forge's non-regular trend into larger n, NOT the circulant family (which I've closed through n=19).

Caveat on my n=13/16 circulant rows below: those are minima over 6-regular CIRCULANTS only. The true
graph-wide min at n=13 is almost certainly lower (forge's trend) but lives among non-circulant graphs;
my 1/40 geng sample of n=13 6-regular found 0 vertex-critical, confirming the 6-regular vertex-critical
population at n=13 is tiny and circulant-dominated, so non-regular (some deg-7/8 vertices) is where the
low-critical n=13 graphs must be — that slice is hunter's scaled campaign + forge's annealer territory.

## Ladder summary (min critical-edge count, by family/regime)
| n  | regime                          | min critical-edge count | note |
|----|---------------------------------|-------------------------|------|
| ≤10| ALL (forge, exhaustive geng)    | 8 (at n=10)             | graph-wide; fraction 64% |
| 11 | exactly 6-regular (FORCED class)| ∞ (no 4-vertex-critical)| ENTIRE Prop-5.1 class, exhaustive |
| 13 | 6-regular circulant             | 13 (C13(1,2,5); plateau)| one orbit; non-circ n=13 lower but rare |
| 16 | 6-regular circulant             | 16 (C16(1,2,5))         | diff-1 orbit, fraction 1/3 |
| 19 | 6-regular circulant             | 19 (C19(1,2,5))         | one orbit; route closed |

The minimum has NOT hit 0 anywhere checked. The circulant family floors at n/3 critical edges and is
locally rigid. A witness (0 critical edges), if it exists, must come from OUTSIDE the circulant basin
— consistent with wall's circulant impossibility direction and the squad's 0-witness floor (n≤10
exhaustive by hunter/skeptic; n=11 exhaustive here).

## Coordination
- Plateau finding → count (your SA needs non-local escape from the circulant basin) and wall
  (corroborates your mod-3 rigidity theorem direction empirically: local moves can't release diff-1).
- Structural SAT model → hunter (complement to geng for large-n regime; min-deg≥6 + Δ≤n−5 + K4-free
  encoded, λ≥6 post-hoc).

### RESULT 5 — critical-orbit count vs triangle-freeness at n=31 (with wall's cocycle mechanism)

Tested wall's prediction "2-critical-orbit ⟺ triangle-free connection set" over ALL 120 vertex-critical
6-regular circulants at n=31 (dual-checked: χ + vertex-criticality + per-edge criticality + triangle
test). Result — the FORWARD direction holds, the converse fails:

| #critical-orbits | triangle-free | count |
|------------------|---------------|-------|
| 1 | has-triangle  | 60 |
| 1 | triangle-free | 45 |
| 2 | triangle-free | 15 |
| 2 | has-triangle  | 0  |

- ✅ **2-orbit ⟹ triangle-free: CONFIRMED 15/15** (zero 2-orbit cases have a triangle). Matches wall's
  ℤ₃-coloring-uniqueness mechanism: triangles ({1,2}-type) force a near-unique 3-coloring whose single
  mono-edge sits in one orbit; only triangle-free sets admit the MULTIPLE colorings that can split
  singleton mono-edges across two orbits.
- ❌ **triangle-free ⟹ 2-orbit: FALSE** — 45 triangle-free circulants are still ONE-orbit. Triangle-
  freeness is NECESSARY but NOT SUFFICIENT for ≥2 critical orbits.

CLEAN STATEMENT: "≥2 critical orbits ⟹ triangle-free connection set" (empirical, n=31). The 1-vs-2
split among triangle-free sets (45 vs 15) is governed by a finer condition (wall's f(G) / the ℤ₃-
coloring structure), not mere triangle-freeness. Does NOT affect the headline (all 120 have
critical-count ≥ n > 0, so no witness); this is mechanism, refining wall's circulant impossibility.

### RESULT 5b — one→two orbit transition is bracketed to n ∈ {28, 31} (with wall; closed)
Verified: n≤25 ALL one-orbit (n=22: 15 vc-circulants, n=25: 60, all single-orbit); two-orbit cases
EXIST by n=31 (15 of 120 vc-circulants, all triangle-free per Result 5). So the first two-orbit
appearance is in n ∈ {28, 31}. The exact transition n is NOT load-bearing (wall confirmed): whether 28
or 31, the correction stands and the headline "no 6-regular circulant witness, n≤31" is intact. The
only UNIFORMLY-true circulant statement is "critical-count ≥ n > 0 ⟹ no witness" (robust to n=31).
The exact transition is a cheap known follow-up (n=28, ~325 sets) if ever needed for a writeup — NOT
run, by wall's steer (not worth the compute). Circulant correction thread CLOSED, reconciled across
proximity + wall + skeptic.

### RESULT 6 — SEARCH SIDE SATURATED (capstone, joint with count, 2026-06-10)

count ran the artifact-free ENC-11 variant I designed (n=13/14, δ=6 at ≤50% density = ROOM, explicitly
asymmetric + anti-regular = no symmetry). The wall HELD: no witness, no sub-n/3 feasible hit. This
RULES OUT the two candidate artifacts (cramming, symmetry) — the (vertex-criticality ⊥ no-critical-edge)
trade is INTRINSIC, not an artifact.

CONSOLIDATED SEARCH-SIDE VERDICT (maximally robust; all dual-checked; HEURISTIC, not proof):
No (4,1)-witness is reachable by ANY tested variation —
  - basin: circulant, Mycielski/WALL-5, random-6-regular, forge n=10 champion, union-construction
  - granularity: single-edge moves AND multi-edge coordinated batches
  - density: cramped (n=10) AND roomy (n=13/14, ≤50% density)
  - symmetry: orbit-locked AND explicitly asymmetric/anti-regular
Every controlled variation → the same negative. The search lands on the (critE, non-critical-vertex)
trade curve and cannot reach its (0,0) corner. This is the empirical content of the conjectured lemma
"no graph is simultaneously δ≥6, vertex-critical, and critical-edge-free."

⟹ The search side has done its job (bounded the problem; removed every artifact explanation). RESOLUTION
NOW REQUIRES A STRUCTURAL PROOF, not more search. Two live routes:
  1. wall's f-invariant / ℤ₃-coloring min-conflict argument (prove min-conflict ≥ 2 is forced).
  2. The global-obstruction EXISTENCE route (ℤ₃-tension on a triangulation, Youngs-analog) — the only
     untested existence route, since it builds the witness topologically rather than reaching it by
     local/SA moves. If it yields a candidate, the quadruple-confidence gate (floor_worker/checkers +
     skeptic chi_A/chi_B + proximity incremental verifier) is armed.

### RESULT 7 — coloring-discriminant for orbit-count + k=5 boundary (for the impossibility lemma)

Two findings anchoring the circulant impossibility lemma (joint with forge's common-root/Potts frame):

(a) DISCRIMINANT (n=31, all 60 triangle-free vc circulants; essentially-distinct 3-colorings of G−v0
    = #total/6 via exact SAT enumeration):
    | #crit-orbits | #ess-distinct colorings | count |
    |---|---|---|
    | 1 | 1 | 33 | (rigid)
    | 1 | 2 | 2  |
    | 1 | 4 | 8  | ← multiple colorings, STILL one orbit
    | 1 | 5 | 2  |
    | 2 | 2 | 10 |
    | 2 | 8 | 4  |
    | 2 | 11| 1  |
    - 2-orbit ⟹ ≥2 essentially-distinct colorings: CONFIRMED 15/15.
    - ≥2 colorings ⟹ 2-orbit: FALSE (12 one-orbit cases have ≥2 colorings, up to 5, all landing in ONE
      orbit). So the discriminant is the ORBIT-LOCATION of each coloring's singleton mono-edge, NOT the
      coloring count. #critical-orbits = #{distinct orbits hit by singleton-mono-edges across colorings}.

(b) k=5 BOUNDARY (the lemma's q=3-specificity, verified): C17(1,3,4,5) is a 5-VERTEX-CRITICAL circulant
    with ZERO critical edges (8-regular, 68 edges) — a k=5 circulant WITNESS. So "no 6-reg circulant is
    a (4,1)-graph" CANNOT be a generic claim (false at k=5, consistent with Brown/Jensen). It is
    q=3-SPECIFIC: the orbit-persistence that forces a critical orbit at k=4 is a 3-COLORING phenomenon
    that breaks at k=5. The lemma is "no 6-regular circulant is a (4,1)-graph because the ℤ₃-coloring
    structure forces ≥1 critical difference-orbit (x=3 a non-common-root of {P(G−e,x)})."

These feed forge's common-root frame: critical-count > 0 ⟺ ≥1 difference-orbit has x=3 as a NON-root;
orbit-persistence (n≤31) says this ALWAYS holds for 6-reg circulants; the discriminant says how many
orbits; the k=5 boundary fixes the q-specificity. Circulant lemma of the impossibility proof.

### RESULT 8 — |E*| extremal profile: circulants are WORSE than irregular minimizers (symmetry-cost)

Cross-check for forge's non-circulant frontier (joint impossibility doc §3/§4). Min |E*| (critical-edge
count) over 4-vertex-critical CIRCULANTS (any connection set) by n, vs forge's all-graph frontier:

| n | min|E*| over 4-vc circulants | forge non-circulant frontier |
|---|---|---|
| 7 | 7 (C7(1,2)) | 7 | (coincide — C7(1,2) IS the extremal)
| 8 | none | 12 |
| 9 | none | 9 |
| 10| 10 (C10(1,2)) | 8 | ← circulant HIGHER by 2
| 13| 13 | - |
| 16| 16 | - |
| 19| 19 | - |

- 4-vc circulants exist ONLY at n ≡ 1 mod 3 (n=7,10,13,16,19 in range), and where they exist,
  min |E*| = n EXACTLY (one full difference-orbit).
- At n=10 the irregular minimizer reaches |E*|=8 but the best circulant is stuck at 10. So SYMMETRY IS
  A HANDICAP on the |E*| axis: the orbit structure pins |E*| up at n, while irregular graphs spread the
  criticality thinner. forge's non-circulant frontier DECREASES (12→9→8); circulants stay AT n. The two
  regimes diverge, and the witness (|E*|=0) is in NEITHER.
- Feeds the joint impossibility doc: confirms the symmetry-cost asymmetry (orbit-locking forces a full
  critical orbit), complementing the non-circulant base.
