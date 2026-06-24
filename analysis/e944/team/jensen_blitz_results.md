# jensen INVENTION BLITZ — full results (overflow of INVENTIONS.md, kept here to avoid edit races)

Design constraint (skeptic-vetted): edge-redundancy from SEPARABLE PARALLELISM (literal disjoint rails)
→ rail vertices non-critical. Build ENTANGLED density (δ≥6, reroutes share neighborhoods). ℤ₃-tension-first
where possible. χ via harness.py (2 engines) cross-validated vs checkers.py. Target: 4-vertex-critical,
0 critical edges. Code: jensen_code/blitz_round1.py, blitz_round2.py.

⚠ STATUS OF "ENTANGLEMENT" (2026-06-11, verified twice — read before using it):
"Entanglement vs parallelism" is an INFORMAL SEARCH INTUITION ONLY — it is NOT a computable per-edge
discriminator, and NO simple local metric realizes it. Verified two independent ways:
(1) obstruction_family.py: the k=5 WITNESS G_5,2,2 has CUT-PAIR (tree-like) minimal obstructions while
    NON-witnesses (C13, J–S) have 2-edge-connected ones — OPPOSITE of the hypothesis.
(2) per-edge metric sweep: in C13(1,2,5) the CRITICAL edges have MORE common-neighbors (2) than the
    NON-critical ones (0-1) — entanglement-by-common-neighbors is BACKWARDS; local-edge-conn is constant
    (6) across both, can't separate them.
⟹ "rail-like ⟹ not a witness" is FALSE as a per-edge structural criterion. Do NOT build a diagnostic on
it (told forge; retracted from proof framing). It survives ONLY as loose design intuition for search.
The REAL discriminators are GLOBAL: wall's spanning-obstruction lemma + gallai's q=3 P(G−e,3) zero-free —
consistent with the obstruction being an irreducibly global q=3 coloring CSP (gallai), not anything local.

## ROUND 1
- **J1 wheel-web** (h pairwise-adj hubs + odd rim, hubs↔all rim): DEAD. h=2→χ=5, h=3→χ=6 overshoot
  (hub adjacent to all of odd rim forces rim 2-colored = impossible). = algebra's C6 two-hub overshoot,
  cross-confirmed. δ=4 too low.
- **J2 antiprism stack** (triangulated cylinder): PARTIAL → χ=4 but not vertex-critical, δ=4 < 6.
- **J3 complement of C_n**: PARTIAL → n=8 χ=4 (not vc); n≥9 χ=5,6 (too dense). δ=6 at n=9.
- **J4 dihedral Cayley** (NON-ABELIAN): D7 n=14 χ=4 (not vc); D6 χ=2. ⚠ DOWNGRADED by skeptic: NOT a
  fresh escape. Orbit lemma (edge-criticality constant on each Aut-orbit) applies to EVERY vertex-transitive
  graph, and ALL Cayley graphs (abelian AND non-abelian) are vertex-transitive → non-abelian Cayley edges
  are still generator-orbit-uniform = SAME circulant trap. The obstruction is TRANSITIVITY ITSELF, not
  abelian-ness. My "promising/LIVE FRONTIER" label was WRONG — it predates the orbit-lemma synthesis
  (wall WALL-1 + skeptic). Don't pursue transitive Cayley sweeps.

## ROUND 2 (fixes)
- **J4' dihedral Cayley SWEEP** (D7, n=14, δ=6, ~40 conn sets): [orbit-locked, not a novel route — see
  J4 downgrade] STRONG WALL — ~12 hit χ=4 with δ=6 but
  0/12 vertex-critical. Non-abelian δ=6 χ=4 at n=14 consistently fails vertex-criticality. Corroborates
  count (non-abelian Cayley) + hunter (n=14 nulls). DEAD.
- **J2' toroidal antiprism** (+diagonals → δ=8): DEAD. δ=8 but χ overshoots (5,6,8); only n=24 hits χ=4,
  not vertex-critical.
- **J3' complement of C_n(1,4)** (denser tri-free base): DEAD. δ=8,9 but χ=6,7 (complement too dense).
- **J5 ℤ₃-tension circulant** C₁₃(1,5),C₁₃(2,3): χ=4, vertex-critical, 0 bridges, BUT δ=4 + 26/26 critical.
  Overlaps count; not new. Confirms: vertex-critical circulants are exactly the δ=4 sparse ones.

## VERDICT (jensen blitz, both rounds; corrected per skeptic's orbit-lemma adjudication)
Two distinct walls, NOT one repeated:
- **TRANSITIVE substrates** (circulants, abelian + NON-abelian Cayley J4/J4'): orbit-locked — criticality
  is constant on each Aut-orbit, so #critical = (full orbits); never 0 with vertex-criticality. This is
  ONE wall (transitivity), so J4 is NOT an independent confirmation — it's the same circulant trap (skeptic).
- **ASYMMETRIC density** (J2' toroidal, J3' complement, J6 twisted-with-chords): the genuinely different
  regime. Here δ≥6 + χ=4 ⟹ not-vertex-critical (J2'/J3'), and the vertex-critical ones are δ=4 sparse
  fully-critical (J5) or asymmetric-but-floored (J6 → 13 critical at n=13). This is the REAL choke point.
NET: no STRUCTURED family (transitive OR the asymmetric-but-still-modular ones I tried) is vertex-critical
+ edge-redundant at χ=4. Per skeptic, the right place to keep pushing is ASYMMETRIC density (not transitive
sweeps); J6 (asymmetric chords on a vertex-critical seed) was the correct instinct and got furthest
(26→13 critical, vertex-critical preserved). The witness, if it exists, is NON-transitive (|Aut|=1),
non-modular, expander-like dense — global search (hunter/forge) — OR it doesn't exist (wall/gallai
impossibility, esp. gallai's E*≠∅ ⟺ Σ_e P(G−e,3) > 0 q=3 Potts route).

## ROUND 4 (jensen, 2026-06-10) — asymmetric greedy densification (skeptic's pivot) — blitz_round4.py
Directly pursued skeptic's "push asymmetric density, not transitive sweeps." Greedy: from a vertex-critical
χ=4 seed, repeatedly add the chord that most reduces #critical-edges while preserving χ=4 ∧ vertex-critical.
- C₁₃(1,5) and C₁₃(2,3) seeds (δ=4, 26 critical): drop 26 → 16 → 13, then STALL HARD at 13 — no chord
  reduces further while keeping vertex-criticality. Trajectory [26,16,13].
- C₁₃(1,2,5) (δ=6, already 13) and C₁₆(1,2,5) (δ=6, 16): NO improving chord exists at all (already floored).
- VERDICT: greedy asymmetric densification — the most direct form of skeptic's recommended regime — hits
  EXACTLY the 13-floor at n=13 and provably cannot break it (exhaustive single-chord check at each step).
  This is a 6TH independent method on the 13-floor (mine, hunter, count, skeptic, wall, +this greedy). The
  floor coincides with the δ=6 C₁₃(1,2,5), so it is NOT a δ-artifact. At n=13, no graph beats 13 critical
  edges via local densification; the witness (if any) needs larger n, unreachable by greedy/local search.

My structured-family invention lane is converging to NULL — which is itself the convergent squad result:
the witness is not a nameable construction. Further blitz rounds in this lane would re-derive the same wall.

## ROUND 3 (jensen, 2026-06-10) — IRREGULAR/ASYMMETRIC dense — code: jensen_code/blitz_round3.py
Pivoted off vertex-transitive families (all dead) to genuinely irregular constructions:
- **J6 twisted circulant + asymmetric chords** (MOST INFORMATIVE): adding 1–4 asymmetric chords to a
  vertex-critical δ=4 circulant KEEPS vertex-criticality AND reduces critical edges: C₁₃(2,3)+2 chords →
  **13 critical of 28** (down from 26/26 bare), δ=4, 0 bridges, χ=4 vertex-critical. The asymmetric
  densification navigates the trade PARTWAY (26→13) but never to 0, and can't lift δ past 4. The floor
  it hits — **13 critical edges at n=13** — INDEPENDENTLY matches hunter's annealing optimum, count's
  C₁₃(1,2,5), and skeptic's exhaustive 6-regular optimum. FOURTH independent convergence on "min 13
  critical edges at n=13."
- **J7 random 6-regular filtered χ=4**: 0/60 samples χ=4 vertex-critical. The witness is measure-zero
  in the dense regime — random dense graphs are χ≠4 or not vertex-critical.
- **J8 two cross-linked cores (asymmetric bridges)**: no χ=4 vertex-critical (over-densifies or breaks
  criticality).

**Round-3 verdict:** even irregular/asymmetric densification (the one regime structured families don't
cover) hits the SAME 13-critical-edge floor at n=13 as every other method. The min-critical-edge count
does NOT reach 0 by any construction or search the squad has tried; it plateaus at 13 (n=13), matching
4 independent methods. Either the witness lives at much larger n (beyond reach of construction+search) or
it does not exist. My invention lane is exhausted; the decisive question is now wall/gallai's impossibility
reformulation (Σ_e P(G−e,3) > 0).

## THEORETICAL UNIFICATION (wall + jensen, 2026-06-10) — construction side = impossibility side
wall's spanning lemma: every 4-chromatic subgraph of a vertex-critical G is SPANNING; a 4-chromatic
subgraph avoiding vertex v exists ⟺ v is non-critical. **My construction failures ARE this lemma firing
from the build side:** verified χ(H''−v)=4 (double-gadget) = "B∪G_b is a 4-chromatic subgraph avoiding
G_a's interior ⟹ those vertices non-critical." VERIFIED: single modular J–S gadget has E* CONNECTED +
SPANNING (m=2: 63 edges touch all 46 vtx; m=3: 90 touch all 67). Parallelized modular gadget either breaks
vertex-criticality OR its 4-critical subgraph strips to the single spanning-E* gadget. ⟹ a MODULAR
construction can NEVER reach E*=∅.

DESIGN PRINCIPLE (wall, confirmed by my blitz): a witness must be GLOBALLY edge-redundant yet LOCALLY
vertex-rigid (no localized substructure independently 4-chromatic) = distributed/EXPANDER-LIKE, not
modular. k=4-specific (passes k=5): k=5 has slack (4 classes, δ≥8) so modular redundancy coexists with
vertex-essentiality; k=4 (3 classes, δ=6, forced 2-2-2) has NO slack. Cleanest WHY for the squad's k=4 wall.

ONE UNTESTED CORNER (my J7 sampled only shallowly): expander-like / Ramanujan-style δ=6 graphs (random
lifts, non-modular, |Aut|=1) — the regime the design principle points to. Offered to wall.

## RESIDUAL-SURGERY local-minimum check (jensen, per wall) — residual_surgery.py
wall's caveat: random 6-regular graphs are NEVER vertex-critical (over-robust, off threshold); witness must
be threshold-tight, reached by criticality-PRESERVING densification (WALL-5), not random sampling. I built
residual-surgery (local moves — add / 2-swap / entangle-rewire near each residual critical edge — accepted
only if χ=4 ∧ vertex-critical preserved AND #critical drops) and ran it on n=13 plateaus (awaiting wall's
n=19,23 seeds):
- C₁₃(2,3)+2chords (δ=4, 13 critical): STRICT LOCAL MINIMUM — no local move reduces #critical.
- C₁₃(1,2,5) (δ=6, 13 critical, the canonical convergent optimum): STRICT LOCAL MINIMUM — same.
⟹ BOTH sparse and dense δ=6 n=13 plateaus are genuine local minima of the residual-surgery move set; the
13-floor is robust to local threshold-tight surgery from multiple starts (complements count's pair-move SA).

WALL'S n=19,23 SEEDS — RAN (residual_surgery_wallseeds.py), prioritizing low-degree-incident critical
edges + degree-raising adds per wall's guidance. Both seeds independently re-verified on my harness
(χ=4, vertex-critical, critE 24/27 — matches wall's dual-checker exactly):
- n19_mycC9 (24 critical, δ=3): descended 24→23 (one swap) then STRICT LOCAL MINIMUM. Floor ≈ n+4 = 23. ✓
- n23_mycC11 (27 critical, δ=4): descended 27→26→25 then STRICT LOCAL MINIMUM. Floor ≈ 25 (≈n+2..4).
NO WITNESS. The floor does NOT soften as n grows 13→19→23; it stays a strict local minimum from my
move family (genuinely independent of count's balanced pair-swaps + wall's WALL-5/7: mine targets
low-degree-incident edges and raises degrees). ⟹ a 4TH independent local-search family confirms the
≈n+4 floor is a strict local-search BARRIER across n=13,19,23. Strong combined impossibility intel
(jensen residual-surgery + count pair-move + wall WALL-5 + WALL-7, all stuck at ≈n+4 from threshold-tight
basins). Consistent with: no nameable/local-reachable witness; answer leans hard NO.
WHY it strengthens (not softens) with n (wall): dense δ≥5 f≥2 graphs have absorber-fraction ~0.2 — LOWER
than sparse — so the "over-full / non-vertex-critical" corner that blocks descent is MORE dominant at
larger n. de-criticalizing a residual edge by raising degrees pushes INTO that corner. My n=19,23 strict
minima confirm wall's prior: the basin barrier is robust and HARDENS as n grows. This is the cleanest
"robust local-search barrier across n" result for the impossibility writeup.

THE 13-FLOOR — SIX independent methods (skeptic's enumeration, 2026-06-10):
(1) skeptic exhaustive Problem-5.2 sweep (C₁₃(1,2,5) = unique 6-reg 4-vc graph, min=13);
(2) count basin-hopping (15 hops, never <13); (3) proximity local rigidity (39 adds + 416 swaps pinned);
(4) wall WALL-5 edge-addition (Grötzsch 20→13); (5) wall WALL-7 add-delete cycling (same plateau);
(6) jensen greedy chord-addition (asymmetric, 26→13) + residual-surgery (strict local min both plateaus).

## COCYCLE INVARIANT f(G) — construction-side evidence for wall's impossibility object (verified) cocycle_f.py
wall's invariant: f(G) = min over 3-colorings of #monochromatic edges. witness ⟺ f≥2 ∧ vertex-critical;
impossibility = "vertex-critical χ=4 ⟹ f≤1". I computed f exactly (backtracking + branch-bound) and
VERIFIED the connection f(G)=1 ⟺ E*(G)≠∅ on every test (K4, C₁₃(1,2,5), J–S H(m=2), J6 asymmetric):
0 mismatches. C5 (3-colorable) → f=0. CONSTRUCTION-SIDE FINDING: **every vertex-critical χ=4 graph the
whole squad can build has f(G)=1** — single modular J–S gadget (f=1, |E*|=63), C₁₃(1,2,5) (f=1, the
δ=6 floor graph), J6 asymmetric chord-graph (f=1, 13 critical). None reaches f≥2. So "modular/structured
⟹ f=1" is the cocycle face of my construction nulls, giving wall's impossibility a sharp target:
prove vertex-critical χ=4 ⟹ f≤1 (= q=3 Potts B₁>0, gallai's route). The f≥2 region is empty for every
nameable family — consistent with impossibility.

CALIBRATION (wall, 2026-06-10 — what the f-evidence DOES and DOESN'T do):
- DOES: f(G) is a cheap WITNESS-DETECTOR. Any search candidate (forge/hunter) with f≥2 AND vertex-critical
  IS a witness — flag instantly, wall cross-verifies, skeptic adjudicates. Use f as the verification gate
  on every candidate (faster than the full edge-criticality sweep). This is my STANDING ROLE going forward.
- DOESN'T: more f=1 observations do NOT prove f≤1. wall+gallai closed the last non-circular impossibility
  lever (cocycle-RANK angle FAILS: v absorbs ⟺ G−v's cut space has a nowhere-zero vector = 3-colorability,
  not a rank property; absorbers aren't independent, no α-cap). So "every buildable graph has f=1" is
  evidence of EQUIVALENT DIFFICULTY to Dirac k=4 — the conclusion restated, not a proof. The empty f≥2
  corner is what we'd see whether the answer is "no witness" OR "witness exists but isn't nameable/modular."
- NET: f-gate = high-value verification instrument for the existence search; the existence search itself
  (threshold-tight, non-modular, criticality-preserving densification — NOT random sampling) is the live
  frontier. No witness found anywhere; verdict remains honestly OPEN, leaning hard toward NO.

## JOINTLY-NECESSARY REGIME — REALIZABLE but STILL trades off (jensen, verified) jointly_necessary.py
wall said "no logical obstruction" to jointly-necessary spanning redundancy; the barrier is realizability.
I built it and confirmed BOTH halves precisely (m=2, shared star + B, two weakened partial gadgets):
- **Jointly-necessary IS achievable as a coloring property:** two 2-chain gadgets (e.g. chains{1,2} +
  chains{1,3}) are EACH individually 3-colorable with B [χ(B∪G_a)=χ(B∪G_b)=3] yet their UNION is
  4-chromatic [χ=4]. So "neither alone sufficient, together sufficient" is real.
- **But it STILL can't reduce |E*| AND stay vertex-critical:**
  · 2-chain + 2-chain (chains overlap, e.g. {1,2}+{1,3}): |E*|=43 < single-gadget 63 (REDUCTION!) but
    NOT vertex-critical — 20/56 vertices non-critical, EXACTLY the internal vertices of the SHARED chain
    (chain 1, in both gadgets), 10 from each copy. The duplication of chain 1 de-criticalizes chain-1
    edges AND frees chain-1 vertices — same effect, inseparable.
  · 2-chain + 1-chain (chains partition to exactly {1,2,3}, e.g. {1,2}+{3}): vertex-critical BUT |E*|=63
    (no reduction — the 1-chain adds no redundancy, it's the single gadget relabeled).
- VERDICT: the |E*| reduction comes EXACTLY from chain-duplication, and chain-duplication frees exactly
  that chain's vertices. Mutual coverage on a shared chain = separable parallelism on that chain. The
  jointly-necessary escape is realizable as a coloring but does NOT escape the redundancy↔vertex-criticality
  trade. Confirms wall's "realizability, not logic" + my entanglement dichotomy at the finest resolution.
  Answers forge's mutual-cover: the deciding test is whether the two gadgets SHARE a chain — shared chain
  ⟹ |E*| drops there but those vertices die; disjoint chains ⟹ no reduction.
