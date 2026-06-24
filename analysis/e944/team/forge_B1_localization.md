# forge — per-vertex localization of B₁ (proof-team contribution, 2026-06-10)

Target (proof team): χ=4 vertex-critical ⟹ B₁ = Σ_e P(G−e,3) > 0 (= no witness).
gallai's frame: B₁>0 ⟺ x=3 is a SIMPLE (not double) root of P(G,x). My contribution
localizes B₁ to vertices, putting it in reach of the deg-3 theorem + per-vertex lemma.

## Verified identity (exact, ratio=2.000 on all tested 4vc graphs)
> **Lemma (forge).** B₁(G) = ½ Σ_v cnt(v), where for each vertex v,
> cnt(v) := #{ proper 3-colorings φ of G−v : in φ, exactly ONE color is a
>   SINGLETON among N(v), AND the other two colors each appear ≥1 time in N(v) }.
>
> Proof idea: a B₁-coloring is a 3-coloring of G monochromatic on exactly one edge
> uv. Restricting it to G−u is a proper 3-coloring of G−u in which u's color is a
> singleton in N(u)·… symmetric at both endpoints — each B₁-coloring is counted at
> exactly its 2 endpoints, hence the factor ½. (The "other two colors appear"
> condition ensures v genuinely had no proper color, i.e. the coloring is mono-1
> not mono-0.) Verified: Σ_v cnt(v) = 2·B₁ exactly on all 4vc graphs n=7 tested.

## Why this helps the proof
- It converts the global "B₁>0" into "**∃ vertex v with cnt(v) > 0**" — a LOCAL
  per-vertex statement about 3-colorings of G−v and the color-multiset on N(v).
- cnt(v) > 0 ⟺ v is incident to a critical edge (forge per-vertex lemma): a color
  appearing as a singleton in N(v) under a 3-coloring of G−v is exactly the
  witness that the edge v–(singleton carrier) is critical.
- So "B₁ > 0" ⟺ "some vertex has cnt(v)>0" ⟺ "some vertex has a critical edge"
  ⟺ "E* ≠ ∅" — consistent (it's the same statement), BUT now phrased as a SUM of
  non-negative per-vertex counts, so a lower bound on ANY ONE cnt(v) closes it.

## The remaining hard core (honest) + where my theorems bite
- DEGREE-3 case: if any vertex v has degree 3, then (forge deg-3 theorem) all 3
  edges at v are critical, so cnt(v) ≥ 1 ⟹ B₁ > 0. DONE for δ=3.
- The witness must have δ≥6 (SkSt). So the open core is: for a δ≥6 χ=4
  vertex-critical graph, prove SOME cnt(v) > 0. Equivalently (wall's criterion
  negated): it is NOT the case that every vertex v has every 3-coloring of G−v
  COLOR-BALANCED on N(v) (each color ≥2).
- This is exactly the "all-good CSP" gallai/wall identified as the irreducible
  core — but the localization gives a clean ATTACK: bound cnt(v) below using the
  STRUCTURE of N(v). For δ≥6, |N(v)|≥6 and a proper 3-coloring of G−v splits N(v)
  into 3 color classes summing to ≥6; "all ≥2" is a strong balance condition. The
  question is whether the GLOBAL 3-coloring constraints can force perfect ≥2-balance
  at EVERY vertex simultaneously — gallai's zero-free-region / Potts-root attack.

## Hand-off
- gallai: B₁ = ½Σ_v cnt(v) plugs into your Z(G,t) double-root frame — the
  per-vertex cnt(v) is the t=0 derivative localized; a per-vertex lower bound gives
  the simple-root (B₁>0) result.
- wall: cnt(v)>0 ⟺ your witness-criterion FAILS at v; "∃v: cnt(v)>0" is the exact
  negation of "every vertex good." The localization makes the ℤ₃-tension a SUM of
  per-vertex tensions.
- skeptic: k=5 reality check — at q=4 (k=5) the analogue cnt₄(v) CAN be 0 at every
  vertex (real (5,1)-witnesses exist), so any lower bound on cnt(v) MUST use a
  q=3-specific fact (e.g. |N(v)|≥6 with only 3 classes ⟹ pigeonhole pressure that
  q=4 with ≥... does not have). That pigeonhole gap is the q=3-specific lever.

## The discriminating test (unifies forge B₁-localization with count's E* analysis)
count reads "fragmented E*" as existence-leaning; I read "spanning E*" as impossibility.
The CLEAN discriminating question between us: does there exist a 4-vertex-critical graph
with a vertex UNTOUCHED by E* (incident to NO critical edge)?
- Such a vertex v has cnt(v)=0 (wall-balanced). A graph with ALL vertices untouched = witness.
- "E* fragmented" is irrelevant to existence (a witness needs E*=∅, not E* disconnected);
  only "E* non-spanning" (some vertex untouched) moves toward a witness.
Verified: NO E*-untouched vertex in any 4vc graph n=7,8,9 (all vertex-spanning); n=10 sweep
running. If 0 at n=10 too, the vertex-spanning theorem (= every vertex has a critical edge =
B₁>0 localized) holds through n=10 — the impossibility statement, exhaustively, to n=10.
My champion's E* is fragmented (2 comps of size 5) BUT spanning (touches all 10) — fragmentation
does NOT help existence; spanning = not a witness.

## DISCRIMINATING TEST RESULT (n=10, decisive): vertex-spanning holds
Exhaustive over ALL 2453 four-vertex-critical graphs at n=10 (scanned all 5.2M connected
min-deg-3 graphs): ZERO have an E*-untouched vertex. So EVERY vertex of EVERY 4-vertex-
critical graph (n=7,8,9,10) is incident to a critical edge — the vertex-spanning theorem,
= the localized B₁>0 statement (cnt(v)>0 for some, in fact every, v), verified exhaustively
through n=10 with zero exceptions. No 4vc graph has a wall-balanced vertex. Combined with the
~556K |E*|=0 base (all non-vertex-critical), the impossibility statement is exhaustively
confirmed to n=10. The remaining gap is purely the analytic proof for general n (gallai/wall
joint-family zero-free region).

## algebra's "positive fraction" reading, SHARPENED to an absolute count floor
algebra (invention mandate, 3 families: circulant/quasigroup/parity) observed a recurring
~50% redundancy CEILING and posed reading (b): "every structured χ=4 vertex-critical graph
has a positive fraction of critical edges." My vertex-spanning theorem sharpens this and
removes "structured":
  vertex-spanning (every vertex incident to a critical edge, proven exhaustively n≤10)
  ⟹ E* is an EDGE COVER of V ⟹ |E*| ≥ ⌈n/2⌉ (a minimum edge cover has ≥ n/2 edges).
Verified: actual min |E*| ≥ ⌈n/2⌉ at every n (n=10: min 8 ≥ 5). So the IMPOSSIBILITY
statement is the ABSOLUTE COUNT floor |E*| ≥ ⌈n/2⌉ ≥ 1, NOT a fraction floor (the fraction
|E*|/m can →0 as m grows like 3n, but the COUNT cannot drop below ⌈n/2⌉). For a witness you
need |E*|=0, contradicting |E*|≥⌈n/2⌉. So: vertex-spanning theorem (general n) ⟹ no witness.
This is the cleanest absolute form; algebra's fraction-ceiling is the structured-family shadow
of the general vertex-spanning (= B₁>0 localized) statement. The open core remains proving
vertex-spanning for ALL n (the q=3 zero-free-region analytic argument).

## hunter's n≤12 exhaustive floor (2026-06-10) — strengthens the impossibility base
hunter exhaustively closed the FULL δ≥6 IRREGULAR regime at n=12 (degrees {6,7},
Δ≤n−5=7): 4,455,844 graphs, 0 four-vertex-critical, 0 witnesses. Combined with
skeptic's 6-regular n≤14 closure and the general 4vc census, NO (4,1)-witness exists
on ≤12 vertices, period (regular OR irregular). So the vertex-spanning / B₁>0 /
|E*|≥⌈n/2⌉ impossibility statement is now exhaustively verified for ALL relevant
degree regimes through n=12 (and the 4vc-graph census through n=10). The witness, if
any, is n≥13 — and the n=13 case is being closed by hunter (guided annealer) + the
6-regular C13(1,2,5) is the unique 6-reg 4vc graph there, with critical edges.
EXHAUSTIVE FLOOR SUMMARY (impossibility base): no witness n≤12 (all degrees);
no 6-regular witness n≤14; every 4vc graph n≤10 is vertex-spanning (|E*|≥⌈n/2⌉);
all ~556K χ=4 |E*|=0 graphs n≤10 are non-vertex-critical.

## k=5 SOUNDNESS AUDIT (per wall, 2026-06-11) — honest calibration of what's proven
wall's filter: any proof of "|E*|≥1 / vertex-spanning / B₁>0 for all 4vc graphs" MUST break
at k=5 (Brown 1992 witnesses exist ⟹ the statement is FALSE there). Generic vertex-criticality/
density/spanning arguments hold verbatim at k=5 ⟹ unsound. Audit of forge pieces:

1. DEG-3 THEOREM: k=4-specific-SAFE. Proof uses "3 neighbors take 3 DISTINCT colors (all 3 used)."
   k=5 analogue would constrain deg-4 vertices, but G_5,2,2 is 8-regular (δ=2(k-1)=8), NO deg-4
   vertices ⟹ theorem VACUOUS on the k=5 witness ⟹ does NOT wrongly prove k=5. BUT only covers δ=3.
2. PER-VERTEX LEMMA: generic definition-unfolding (holds at any q). SAFE because it CHARACTERIZES
   vertex-spanning, doesn't ASSERT it. (At k=5, G_5,2,2's every G−v 4-coloring is balanced ⟹ the
   lemma correctly gives no critical edge.)
3. VERTEX-SPANNING / |E*|≥⌈n/2⌉ / B₁>0: these are the CONCLUSION (correctly FALSE at k=5: G_5,2,2
   has |E*|=0, not vertex-spanning). My exhaustive verification (n≤12) is DATA, NOT a proof. The
   deg-3 theorem proves the conclusion ONLY at δ=3. For δ≥6 I have NO k=4-specific proof.

HONEST VERDICT: forge's contributions are SOUND but PARTIAL/REDUCTIONS. They (a) prove the δ=3 case
(k=4-safe), (b) give the correct localization B₁=½Σcnt(v) and family-common-root reformulation
(generic, safe, problem-reducing), (c) supply the exhaustive empirical base (n≤12, data not proof).
The REAL theorem — δ≥6 4vc graphs are vertex-spanning at k=4 but G_5,2,2 escapes at k=5 — needs a
genuinely q=3-specific lever (gallai 2-2-2 tightness / ℤ₃-flow / q=3 zero-free region). I do NOT have
it; my work reduces the problem to it. Heed also wall's n=31 lesson: verify any STRUCTURAL claim to
n≥31, not single constructions ("one critical orbit" and "G−v uniqueness" both break at n=31).

## CORRECTIONS (2026-06-11, from squad adjudication)
- WORDING (skeptic): the B₁ lemma's cnt(v) is canonically "#{B₁-colorings whose
  unique monochromatic edge is INCIDENT to v}". The earlier prose "exactly one
  color a singleton in N(v)" caused a mis-parse (skeptic + gallai both hit it,
  got 0 everywhere). Use the "mono-edge-incident-to-v" phrasing. Identity holds
  (ratio 2.000) under the correct reading; skeptic confirmed 0 failures n≤8.
- COUNT RECONCILIATION (skeptic 619 vs forge 130 at n=8): different filters —
  forge used geng -c -d4 (min-degree ≥4, since |E*|=0 ⟹ δ≥4 by the deg-3 theorem,
  so the d4 restriction is WLOG-sound for the |E*|=0 question); skeptic used a
  looser filter (≈ min-deg ≥3 / all connected). Conclusion identical: ZERO
  vertex-critical among χ=4 |E*|=0 graphs at n=8. Scope note for the board: forge's
  130 is the δ≥4 subset (the only relevant one — δ=3 graphs have critical edges by
  the theorem, so can't be |E*|=0 anyway); skeptic's 619 is the superset. Same NO.
- ANALYTIC LEVER CLOSED (gallai+archivist): do NOT compute root locations of
  P(G,x) or second-nearest family roots — B₁ is provably NOT a function of P(G,x)
  (chromatically-equiv graphs differ in B₁), and the joint family collapses to B₁
  at x=3 (Σ of non-negatives = 0 iff each =0; far roots matter, monic). My
  family-common-root reformulation is valuable LANGUAGE, not new traction.
- ENTANGLEMENT DIAGNOSTIC RETRACTED (jensen+forge): no per-edge structural metric
  separates witness from non-witness (in C13 the CRITICAL edges have MORE common
  neighbors than non-critical — backwards). forge_entanglement_diag.py mislabels;
  DO NOT USE. The obstruction is irreducibly global (q=3 CSP).
