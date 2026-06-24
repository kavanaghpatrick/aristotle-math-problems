# E944 — Joining gallai's E*-nonempty attempt (wall)

**E*(G)** = critical-edge set of a 4-vertex-critical G. A (4,1)-witness ⟺ E*(G) = ∅.
The impossibility theorem (Dirac k=4 FALSE) ⟺ **E*(G) ≠ ∅ for every 4-vertex-critical G.**
gallai's census: E* nonempty + spanning for all 4-vc graphs through n=10; "E* connected" REFUTED at n=10.

## 1. THE k=4-SPECIFIC REALITY-CHECK PRINCIPLE  [load-bearing for the whole squad]

> **Any valid proof of "E*(G) ≠ ∅" MUST break at k=5** — because k=5 witnesses provably exist
> (Brown 1992). So the proof CANNOT use only generic vertex-criticality / density / Gallai structure
> (all of which hold verbatim at k=5). It MUST invoke a genuinely k=4-specific fact.

This kills, in advance, every density/counting route (they're k-independent) — consistent with my
finding (and count's) that no counting obstruction exists. It is the single most important filter for
the squad's impossibility attempts: **before believing any E*≠∅ argument, check it fails at k=5.**

The ONLY k=4-specific ingredient available: at k=4 a "good" vertex (all incident edges non-critical)
needs, by gallai Thm 4, degree ≥6 with its neighborhood colored EXACTLY **2-2-2 over 3 colors** in
EVERY 3-coloring of G−v. At k=5 the analogue is 2-2-2-2 over 4 colors (degree ≥8) — strictly more slack.
The 3-color tightness is the whole game.

## 2. THE SIMULTANEITY TENSION (sharpened, with count's mod-3 dichotomy)

A witness must satisfy, at once:
- χ(G−v) = 3 for every vertex v (vertex-criticality: vertex deletion DROPS χ), AND
- χ(G−e) = 4 for every edge e (no critical edge: edge deletion does NOT drop χ).

count's mod-3 dichotomy on C_n(1,2,5) shows the natural 6-regular family realizes the two corners
SEPARATELY and never together:
- n ≡ 1 (mod 3): vertex-critical ✓ but a full Hamilton cycle of critical edges (E* = n edges).
- n ≡ 2 (mod 3): E* = ∅ ✓ but every vertex non-critical (vertex-deletion-robust, χ(G−v)=4) — fails (b) totally.
- n ≡ 0 (mod 3): χ = 3.

So the symmetric family OVERSHOOTS between corners. A witness lives strictly between, off the
circulant axis — the squad's "asymmetric witness" consensus, now with a concrete reason.

## 3. THE all-good GLOBAL CSP (the impossibility target, not closed)

If E* = ∅, EVERY vertex is good: ∀v, ∀ 3-coloring c of G−v, N(v) is 2-2-2. This is an extremely rigid
global constraint system. The impossibility theorem = "this CSP is infeasible together with χ(G)=4."
I could NOT close the CSP into a contradiction. Honest obstruction: the CSP is feasible LOCALLY at
every vertex (the B-core K_{2m,2m,2m} satisfies 2-2-2 everywhere — but it's only 3-chromatic, gallai
Thm 6); the question is whether χ=4 can coexist. That coexistence is exactly the open Dirac k=4 problem
restated — I did not find a k=4-specific global invariant (parity/eigenvalue/homology on the 2-2-2
constraint) that forces a contradiction. Candidate unexplored: a ℤ_3-homology / nowhere-zero-flow
obstruction tied to the 3-coloring being a ℤ_3-tension; this is the natural k=4-specific invariant
(ℤ_3 is special) but I could not make it bite.

## 4. What I contributed to the E* attempt
- The **reality-check principle** (§1): the proof filter that any E*≠∅ argument must break at k=5 —
  this retroactively explains why all density routes (mine, count's) failed and tells the squad to stop
  trying k-independent arguments.
- The **simultaneity framing** (§2) tied to count's dichotomy: witness = the never-realized middle corner.
- The spanning-{H_e} decomposition (wall_impossibility.md §1) feeds gallai's "E* spanning" census fact:
  E* spanning ⟺ no good vertex ⟺ every vertex incident to some critical edge — my H_e family is the
  global object whose edge-intersection IS E* (count verified set-equality on n≤7).

## 5. Honest verdict
Neither assault target closed. The uniqueness lemma is 68/112 proven + exact affine closed form + sharp
triangle-free death point (wall_uniqueness_lemma.md). The E*≠∅ impossibility has NO k-independent route
(reality-check principle) and I found no k=4-specific global invariant to force it. Combined with the
total absence of a counting obstruction, my honest read remains: the answer is more likely YES
(witness exists, asymmetric, 6-regular, color-balanced), and the highest-EV squad move is forge/hunter's
existence search — NOT further impossibility attempts, which keep dying at the k=5 reality check.

## 6. SYNTHESIS with jensen's construction-side tension — the DESIGN PRINCIPLE

jensen verified: overlaying a 2nd INDEPENDENT obstruction to make a gadget edge non-critical also makes
that gadget's interior vertices non-critical (J-S fix provably fails). This IS my spanning lemma:

- **My §1.1 lemma:** every 4-chromatic subgraph of a vertex-critical G is SPANNING. Equivalently, a
  4-chromatic subgraph that AVOIDS a vertex v exists ⟺ v is non-critical (χ(G−v)=4).
- An INDEPENDENT 2nd obstruction (B∪G_b alone 4-chromatic) is exactly a 4-chromatic subgraph avoiding
  G_a's interior ⟹ those interior vertices are non-critical. jensen's failure = the spanning lemma. ✓

**ANSWER to jensen's question** ("can jointly-necessary spanning subgraphs cover all edges while keeping
all vertices critical?"): YES, there is NO logical obstruction — for a family of SPANNING subgraphs,
vertex-criticality is automatic (spanning lemma). The competition is REALIZABILITY: edge-redundancy must
be GLOBAL/distributed, NEVER LOCAL. A localized spare gadget produces a non-spanning 4-chromatic subgraph
⟹ frees its interior vertices. So:

> **DESIGN PRINCIPLE (for forge's existence search).** A (4,1)-witness must be GLOBALLY edge-redundant
> (every edge avoidable by some spanning 4-chromatic subgraph) yet LOCALLY vertex-rigid (no localized
> sub-structure is independently 4-chromatic). Expander-like, NOT modular/gadget-glued. This is exactly
> why EVERY modular construction (Jensen–Siggers, Lattanzio, cover-based) fails at k=4.

**WHY this is k=4-specific (passes the k=5 reality check):** at k=5 a good vertex needs 2-2-2-2 over 4
color classes (deg≥8) — there is SLACK, so modular gadget-redundancy can coexist with vertex-essentiality
(a vertex stays essential via its other 3 color classes even when one gadget's contribution is made
redundant). Witnesses exist. At k=4 only 3 classes / deg-6 / 2-2-2 — NO slack: gadget-redundancy and
vertex-essentiality compete for the SAME tight budget, so localized redundancy always frees a vertex.
This is the genuine k=4-specific obstruction, now expressed as a DESIGN constraint (global-not-local
redundancy) rather than a counting bound — and it correctly predicts both the k=4 difficulty and the k=5
success. It does NOT prove impossibility (global redundancy may still be realizable non-modularly), but
it is the sharpest characterization of the witness the squad has, and the clearest target for forge.

## 7. THE COCYCLE-SPACE REFORMULATION (with gallai) — non-dual, validated ★

Paired with gallai on the ℤ₃-tension angle. The non-dual cocycle identity (no planarity needed):

Define **f(G) = min over ℤ₃-colorings p:V→ℤ₃ of #{monochromatic edges}** (= min #zero-coords of the
ℤ₃-tension t=δp over the cut/cocycle space). Then:
- χ(G)=4 ⟺ f(G) ≥ 1 (no proper 3-coloring).
- **edge e is critical ⟺ ∃ a ℤ₃-coloring whose monochromatic-edge set is EXACTLY {e}** (that coloring
  3-colors G−e). ⟹ G has a critical edge ⟺ f(G)=1 (the f-optimal coloring's single mono edge is critical).
- **THEOREM (validated, 0 mismatches on all 4-vc graphs n=4,6,7):**
  > G is an Erdős-944 (4,1)-witness  ⟺  f(G) ≥ 2  AND  G is vertex-critical.

f(G)≥2 captures EXACTLY the edge conditions (χ=4 ∧ no critical edge); vertex-criticality is the separate
half. This maps precisely onto count's mod-3 dichotomy: the n≡2 corner = "f≥2 but NOT vertex-critical"
(C₁₄(1,2,5): f=2, not vertex-critical — verified); the n≡1 corner = "vertex-critical but f=1". The witness
needs BOTH, and the families realize them separately.

**k=5 reality check (passes):** f_k(G)=min #mono over ℤ_{k−1}-colorings; witness ⟺ f_k≥2 ∧ vertex-critical,
k-uniform. k=5 witnesses exist ⟹ ∃ G with f_5≥2 ∧ 5-vertex-critical. So f≥2 alone is NOT the obstruction
(it's the witness restatement at every k). The k=4-SPECIFIC difficulty: achieving f_4≥2 over ℤ₃ (only 3
colors, rigid cut space) WHILE vertex-critical — at k=5 the 4th color class (ℤ₄ cut space) gives room.

**Why this is the right pairing target (gallai's ask):** it's a non-dual counting/cohomology invariant
(f = min support-complement over the cocycle space), it ties the witness condition to a single integer
invariant f(G), it uses the triangle rigidity globally (triangles force f-contributions: a triangle
contributes ≥1 mono edge under any ℤ₃-coloring iff... — the rigidity bounds f from below locally), and it
passes the k=5 filter. The open problem becomes: **can a vertex-critical graph have f(G)≥2 at k=4?** —
i.e., is the min-monochromatic ℤ₃-cut-deficiency ≥2 compatible with vertex-criticality? This is a clean,
self-contained restatement of Dirac k=4 in cocycle-space terms. NOT a proof, but the sharpest k=4-specific
algebraic handle the squad has, and the concrete object for the wall+gallai joint effort.

## 8. Potts double-root framing (gallai) — verified identity + a load-bearing correction

gallai's unification: Z(G,t)=Σ_k B_k t^k = q=3 Potts partition polynomial = ℤ₃-tension generating
function (B_k = #ℤ₃-colorings with exactly k monochromatic edges). χ=4 ⟹ B₀=0; E*=∅ ⟹ B₁=0; so
WITNESS ⟺ Z(G,t) has a DOUBLE ROOT at t=0. Conjecture (=impossibility): a 4-chromatic vertex-critical
graph's q=3 Potts polynomial cannot have a double root at 0.

VERIFIED: gallai's identity B₁ = Σ_e P(G−e,3) (42=42 on C₇(1,2), 60=60 on C₁₀(1,2,5)). The derivation:
χ=4 ⟹ every proper 3-coloring of G−e has e monochromatic ⟹ proper-3-col(G−e) = colorings with
mono-set exactly {e}; summing over e gives B₁. Sound.

★ LOAD-BEARING CORRECTION (wall, verified): the conjecture "B₀=0 ⟹ B₁>0" is FALSE without the
vertex-critical hypothesis. There are 15 four-chromatic graphs at n=7 with B₀=0 AND B₁=0 (= χ=4, no
critical edge, but NOT vertex-critical — the n≡2-corner analogues). ALL 15 are non-vertex-critical
(verified: 0 vertex-critical among them). So VERTEX-CRITICALITY IS ESSENTIAL to the conjecture — it is
NOT a framing condition that can be dropped; it does real work. gallai's chromatic-polynomial lower
bound Σ_e P(G−e,3) > 0 MUST invoke vertex-criticality as a live hypothesis throughout, or it proves a
false statement. (This mirrors the f(G) reformulation §7: f≥2 alone ≠ witness; need + vertex-critical.)

WHERE THE COHOMOLOGY/CYCLE-SPACE SIDE STANDS (my assignment): B₁ = Σ over CRITICAL edges of P(G−e,3),
so B₁>0 ⟺ ∃ critical edge ⟺ E*≠∅ — equivalent to impossibility. The Potts-root view's potential
leverage is the DERIVATIVE/multiplicity structure, but I have NOT found a MacWilliams-type or cohomology
identity forcing B₁>0 from B₀=0 + vertex-criticality at q=3. The honest state: the framing is elegant
and correctly k=4-specific (q=4 witnesses realize the double root), the identity is verified, but no
proof of B₁>0 has emerged — it remains equivalent to Dirac k=4. The vertex-critical hypothesis is the
ONLY thing distinguishing the 15 false-at-n=7 cases from the conjecture; the proof must exploit exactly
how vertex-criticality interacts with the q=3 cut space.

## 9. The f≤1 proof object (joint w/ algebra+gallai) — VALIDATED reformulation

KEY MEASUREMENT: f≤1 is NOT a local/averaging bound. A random ℤ₃-coloring of a 6-regular graph (3n
edges) gives EXPECTED n mono edges, so generic 6-reg χ=4 graphs have f ~ n (the n≡2 corner C₁₄(1,2,5):
f=2; over-dense: higher). Vertex-critical 6-reg χ=4 collapses f to EXACTLY 1 (C₁₃(1,2,5), C₁₀(1,2,5):
f=1). So the collapse ~n → 1 is ENTIRELY due to vertex-criticality — a purely local degree-6 / averaging
argument cannot reach f≤1 (it bottoms out at ~n). The proof MUST use vertex-criticality globally.

VALIDATED REFORMULATION (f via vertex-localized colorings; f_vlocalized = f_direct, 0 mismatches):
> f(G) = min over vertices v, over proper 3-colorings c of G−v, of  min_{a∈ℤ₃} #{u∈N(v): c(u)=a}.
(Each proper 3-coloring c of G−v extends to a ℤ₃-coloring of G by giving v its least-used neighbor
color a; mono edges = the neighbors colored a, count = the least color-class size in N(v).)

This is the cut-space object with teeth — it invokes vertex-criticality directly (one proper 3-coloring
of G−v per vertex, guaranteed by χ(G−v)=3). The impossibility conjecture f≤1 becomes:

> **∃ vertex v and proper 3-coloring c of G−v with some color appearing ≤1 time in N(v).**

This is EXACTLY gallai's "good vertex / 2-2-2-balance" condition negated: a witness needs EVERY vertex
v, in EVERY 3-coloring of G−v, to have N(v) colored with every color ≥2 times (2-2-2 at degree 6). The
proof target: show a vertex-critical 6-regular χ=4 graph ALWAYS has a vertex+coloring escaping 2-2-2
balance. gallai's triangle rigidity bounds the color distribution in N(v); the joint effort is to show
the global 2-2-2-everywhere CSP is infeasible at q=3 (it's feasible at q=4 — k=5 witnesses — so genuinely
k=4-specific). This is the sharpest, validated, k=5-filter-passing form of the impossibility.

## 10. Absorber-set analysis (joint w/ gallai) — f≥2 SUPPRESSES absorbers

gallai's absorber reformulation (verified): g(v)=min over ℤ₃-colorings of #{mono edges NOT incident to
v}; g(v)=0 ⟺ χ(G−v)=3 ⟺ v is VERTEX-critical ("absorber"). So vertex-critical ⟺ ALL vertices are
absorbers; witness ⟺ f≥2 AND all-absorber. gallai's sharp target: f≥2 ⟹ absorber set is a PROPER subset.

NEW DATA (wall, nauty geng, 4-chromatic graphs):
- n=8: of 241 f≥2 graphs, MAX absorbers = 3/8 (distribution {0:102, 1:126, 2:12, 3:1}). NONE all-absorber.
- Max absorber-FRACTION among f≥2 graphs: n=7 → 1/7, n=8 → 3/8, n=9 → 3/9 (samples). Stays well below 1.
- So f≥2 strongly SUPPRESSES the absorber count: forcing the edge condition (no critical edge, f≥2)
  drives the number of vertex-critical vertices DOWN. This is the structural mechanism behind count's
  three-basin "bounce to over-full" wall (over-full = few absorbers) — now in cocycle language.

This anti-correlation (f≥2 ⟸⟹ few absorbers) is the core obstruction: a witness needs f≥2 AND
all-absorber, but the two pull opposite ways. The proof target: show the max absorber-fraction among f≥2
4-chromatic graphs is < 1 (strictly), i.e. f≥2 forbids all-absorber.

★ HONEST CAVEAT (my n≥31 discipline): the absorber-fraction samples are in the SPARSE edge range
(2n±3 edges), NOT the δ≥6 DENSE regime where a witness must live (e≥3n). So the suppression is verified
sparse, suggestive but NOT conclusive for the dense witness regime. The decisive measurement (handed to
count): max absorber-fraction among f≥2 graphs with δ≥5,6 at n=11,12 — does the suppression hold where
the witness would be? If yes, strong; if the fraction climbs toward 1 in the dense regime, the conjecture
weakens. Not yet a proof — equivalent-difficulty to Dirac k=4 — but the absorber/f anti-correlation is the
sharpest structural handle, and it's k=4-specific (at q=4, f₄≥2 + all-absorber co-occur = k=5 witnesses).

## 11. DENSE-REGIME absorber suppression — caveat resolved, evidence STRENGTHENED

My §10 caveat (absorber data was sparse-range only) is now RESOLVED. Tested δ≥5 (dense, toward the δ≥6
witness regime) f≥2 four-chromatic graphs exhaustively via geng -d5:
- n=8: 13 dense f≥2 graphs, max absorber-fraction = 1/8, witnesses 0.
- n=9: 266 dense f≥2 graphs, max absorber-fraction = 2/9, witnesses 0.
- n=10: 30288 dense f≥2 graphs, max absorber-fraction = 2/10, witnesses 0.

The absorber-fraction in the DENSE regime is even LOWER than sparse (sparse was up to 3/8). So f≥2
suppresses absorbers MORE strongly as density increases — the anti-correlation holds (intensifies)
exactly where a witness must live. 0 witnesses across 30,288 dense f≥2 graphs at n=10. This is the
decisive empirical support for "f≥2 ⟹ #absorbers ≪ n (≠ all-absorber)" in the witness regime, resolving
the §10 honesty caveat in the impossibility direction.

(Note: the exhaustive 6-regular floor at n=14 via geng -d6 -D6 is computationally infeasible in pure
Python — geng's regular-graph stream + per-graph χ-check is too slow; abandoned. The δ≥5 exhaustive
result above is the tractable, decisive substitute — and δ≥5 strictly contains the δ≥6 witness regime.)

## 12. The cocycle-RANK lever (gallai's last non-circular handle) — DOES NOT REALIZE

gallai correctly identified that the combinatorial absorber-count side is CIRCULAR (absorber ∩ f≥2 ⟹
good vertex = Theorem 4; "f≥2 ⟹ some non-absorber" ⟺ E*≠∅, not a reduction). The one potentially
non-circular handle: a cocycle/dimension RANK bound on how many vertices can simultaneously absorb,
independent of the good-vertex count. I worked it; it does not realize, for two concrete reasons:

(a) STAR-COBOUNDARY structure gives nothing. v absorbs ⟺ ∃ coboundary δp vanishing off star(v). If
G−v is connected, the only such δp has p constant on V∖{v}, giving mono count ∈ {0, deg(v)} — useless
for the f=1 distinction. The f=1 colorings come from p NON-constant on G−v, i.e. genuine proper
3-colorings of G−v. So "v absorbs ⟺ G−v's (dim n−2) cut space has a NOWHERE-ZERO vector" — and the
nowhere-zero condition IS 3-colorability (NP-hard), NOT a pure rank/dimension property. A naive rank
bound cannot capture it.

(b) ABSORBER-INDEPENDENCE bound FAILS. The natural rank-type cap "absorber set is an independent set
⟹ |absorbers| ≤ α(G)" is FALSE: among f≥2 graphs with ≥2 absorbers, the absorber set is NEVER
independent (n=8: 16/16 have adjacent absorbers; n=9: 53/53). So no independence-number cap exists.

VERDICT (joint with gallai): the f-cocycle invariant is the cleanest LANGUAGE for the obstruction
(single-integer, q=3-specific, density-dodging, k=5-filter-passing) and it correctly localizes the
problem, but it does NOT escape the global CSP / Theorem 4. Every handle — counting (circular = Thm 4),
density (no obstruction), rank/dimension (3-colorability hides in the nowhere-zero condition), absorber
independence (false) — collapses back to "is E*≠∅?", which is Dirac k=4 itself. The framework is
exhausted on the impossibility side; no non-circular lever survives. The STRONG empirical state stands:
no witness anywhere (exhaustive n≤10 all-degree, n≤13 six-regular, n≤31 circulant; dense δ≥5 f≥2
absorber-fraction ~0.2 with 0 witnesses over 30k+ graphs). Impossibility is honestly out of provable
leverage; the existence search (forge/hunter, threshold-tight non-modular) is the live frontier.

## 13. No local "slide-to-1" mechanism (f-optimal dissection) — confirms global hardness

Tested whether the f=1 minimum is reachable by LOCAL descent (greedy single-vertex recoloring to reduce
mono-edge count). It is NOT uniform: greedy descent gets STUCK at mono≥2 from some starting colorings —
g6=F{cZG: 90/2187 starts stuck above 1; g6=FJe~O: 354/2187 stuck; g6=FEl~? reaches ≤1 from all starts.
So the f=1 minimum exists (these are f=1 graphs) but is NOT a greedy/local-search attractor — there are
local minima at mono≥2 that are not the global min. The "slide a ℤ₃-coloring down to exactly 1 mono edge"
requires GLOBAL rearrangement, no local recoloring rule achieves it.

This independently confirms §12's verdict: the f≤1 fact hides 3-colorability in the nowhere-zero
condition, so there is no local/greedy/rank mechanism — the "can always reach 1" IS the hard global
content. No local lever exists; the framework is exhausted. (Handed the 6 n=7 non-Hamiltonian-E* graphs
+ this dissection to algebra; the only remaining non-vacuous thing to check is a GLOBAL invariant shared
by the f-optimal colorings, but honest expectation is equivalent-difficulty to Dirac k=4.)

## 14. The 3-way tension demonstrated by degree-climbing (count, from WALL-5 seeds)

count ran degree-lifting pair-move from my WALL-5 seeds. Result — the cleanest single-experiment proof
of the 3-way tension:
- n=15 seed (critE=17, δ=4) → climbed to δ=6 AND critE down to 8, but 6 NON-CRITICAL vertices.
- n=19 seed (critE=24, δ=3) → climbed to δ=6 AND critE down to 9, but 8 NON-CRITICAL vertices.

The δ→6 climb directly TRADES AWAY vertex-criticality. The three conditions {δ≥6, vertex-critical,
low-critE} are reachable in any PAIR but NEVER all three, demonstrated by explicit degree-climbing from
asymmetric near-corner seeds. Matches my random-6-reg finding from the opposite direction (δ≥6-dense ⟹
typically not vertex-critical, 0/30). f-identity note: count's best graphs HAVE critical edges (8,9), so
by "critical edge ⟺ f=1" both have f=1 — not the witness corner (witness needs f≥2 = no critical edge).

This is the empirical backbone for the impossibility lemma "no graph is simultaneously δ≥6, vertex-
critical, AND critical-edge-free" — but it remains empirical, equivalent-difficulty to Dirac k=4.
NEXT (handed to count): map the δ∈{4,5,6} Pareto frontier of (min non-critical-vertices) vs (critE).
Predict convex frontier bounded away from (0,0); closest approach around δ=5 (the witness, if any, is
"least far" there). That frontier map is the genuinely new data; the δ=6 corner is a confirmed strict
local min (4 independent move families agree — wall WALL-5/WALL-7, count pair-move, jensen surgery).

## 15. Degree-6 reduction (algebra) — correct framing, but good vertices are LOCALLY constructible

algebra reduced "vertex-critical χ=4 ⟹ f=1" to a degree-6-localized claim: deg(v)≤5 ⟹ min-minority(v)=1
automatically (pigeonhole — can't fit (≥2,≥2,≥2) in <6 neighbors); deg≥6 is the only regime with content.
The reduction is CORRECT (verified: n=13 6-reg graph has all 13 vertices min-minority=1) and useful framing.

BUT the proposed Kempe route (show (2,2,2) is never forced at deg 6) CANNOT close, because (2,2,2) IS
forceable: I enumerated all H on 6 vertices — 2860 force EVERY proper 3-coloring to be 2-2-2 balanced.
And if N(v)'s internal structure is a forcing-H, v is GOOD regardless of the rest (more edges only remove
colorings, all survivors still 2-2-2). Concrete gadget built: H + apex v, χ=4, v's neighborhood 2-2-2 in
all 6 colorings of G−v ⟹ v is a good vertex with no incident critical edge. So a SINGLE good vertex is
trivially constructible. "2-2-2 never forced at deg 6" is FALSE locally.

⟹ the witness obstruction is purely GLOBAL: all n vertices good SIMULTANEOUSLY + consistent colorings +
vertex-critical + χ=4. One good vertex is easy; all-good is the wall. CLEAN LOOP CLOSED: a deg-6
good-vertex gadget IS a localized obstruction = jensen's spare gadget = frees vertices (my spanning lemma,
§6). So good-vertex gadgets exist locally but provably can't tile into a witness. This is the same
irreducibly-global wall as the cocycle-rank lever (§12) — the deg-6 reduction isolates WHERE the content
is (global compatibility of good-vertex gadgets) but doesn't provide a local handle. Logged: don't
enumerate single-neighborhood Kempe-reducibility (it confirms forceability and stalls).

## 16. JOINT IMPOSSIBILITY CLOSURE (wall + gallai) — six angles, six collapses

gallai completed the dense-regime + triangle-structure analysis. Final consolidated state, fully
cross-checked across both our work:

DENSE-REGIME (gallai, confirming my §11): δ≥5 f≥2 4-chromatic — n=8 max absorbers 1/8, n=9 max 2/9, 0
all-absorber witnesses. Even more suppressed than sparse. Anti-correlation holds + strengthens in the
witness regime (suggestive-not-conclusive past exhaustive reach n≤9-10, but trend favorable).

TRIANGLE-STRUCTURE (gallai): absorbers are triangle-RICH and high-degree (avg 10.16 N(v)-internal-edges
vs 5.25 for non-absorbers; the deg-6/7 vertices). DOVETAILS with my §15 deg-6 good-vertex gadget: the
2860 forcing-H neighborhoods are exactly dense triangle-rich 9-edge structures. So "absorber ⟺
triangle-rich neighborhood" from both angles. HONEST NEGATIVE: does NOT contradict — a witness needs every
vertex triangle-rich, which δ≥6 supplies. The triangle structure absorbers need is what a dense witness
provides; no tension.

SIX INDEPENDENT ANGLES, ALL COLLAPSE to the irreducible global all-good CSP = E*≠∅ = Dirac k=4:
1. Counting (absorber-set size) → circular = Theorem 4 good-vertex count.
2. Density (Kostochka–Yancey) → no obstruction (vertex-critical densifies freely).
3. Cocycle-RANK → "v absorbs ⟺ G−v cut space has nowhere-zero vector" = 3-colorability, not rank;
   absorber-independence cap false (n=8 16/16, n=9 53/53 adjacent).
4. Triangle-counting → absorbers want MORE triangles, consistent with δ≥6, no contradiction.
5. Deg-6-local → good vertices LOCALLY constructible (2860 forcing-H), obstruction is global.
6. Local-descent (slide-to-1) → no greedy/Kempe mechanism; global rearrangement required.

FINAL: the impossibility framework is EXHAUSTED, confirmed from both wall and gallai. Produced: cleanest
reformulation (f≥2 ∧ vc ⟺ witness ⟺ Potts double-root), sharpest k=4-specific characterization,
exhaustive dense no-witness evidence — but NO proof. The obstruction is a single irreducible global object.
The existence search is the live frontier.

## 17. WITNESS-REGIME absorber suppression (count, n=11 δ≥6) — decisive empirical backbone

count measured the absorber-fraction in THE witness regime (δ≥6, n=11), validated f/absorber defs vs
K4 + C₁₃(1,2,5):
- n=11, δ≥6: 876 f≥2 four-chromatic graphs. MAX absorber-fraction = 1/11 ≈ 0.091. Distribution
  {0 absorbers: 863, 1 absorber: 13}. ZERO all-absorber (witness).
- n=11, δ≥5: identical — max 1/11, 0 all-absorber, 867 f≥2 graphs.

THE TREND, full progression (max absorber-fraction among f≥2, by regime):
  sparse n=8→0.375, n=9→0.333 | δ≥5 n=8→0.125, n=9→0.222, n=10→0.200 | δ≥6 n=11→0.091.
So as we move INTO the witness regime (denser, larger n), the absorber-suppression INTENSIFIES — 98% of
δ≥6 f≥2 graphs at n=11 have ZERO absorbers. The two witness conditions (f≥2 AND all-absorber) are
MAXIMALLY anti-correlated exactly where a witness must live. A witness needs the absorber-fraction to JUMP
from ~0.09 (dense max) to 1.0, and density pushes it the WRONG way.

This is the cocycle-language quantification of count's three-basin "bounce to over-full" wall, now in the
witness regime. HONEST CAVEAT (count): n=11 δ≥6 is random-sampled (not nauty-exhaustive), so a measure-zero
witness needle could be missed — NOT a proof. But 876 f≥2 graphs at exact witness parameters with near-
total (98%) absorber suppression is the strongest empirical backbone the impossibility lemma has. n=12
running. This + the six-angle framework exhaustion (§16) is the complete impossibility-side state: cleanest
reformulation, sharpest k=4-specificity, decisive witness-regime no-witness evidence — no proof, answer open.

## 18. The deg-6 lemma is "never FORCED" not "excluded" — HCQbfrm counterexample

algebra asked whether the deg-6 step is "(2,2,2) split IMPOSSIBLE in a 4-vc graph" (excluded) or
"(2,2,2) possible but always escapable to min-1." RESOLVED: it's the second.

COUNTEREXAMPLE (verified): g6=HCQbfrm (n=9, 18 edges, χ=4, VERTEX-CRITICAL). Its degree-6 vertex v=8 has
N(v) splits {(1,2,3), (2,2,2)} over proper G−v colorings — so (2,2,2) DOES occur at a deg-6 vertex in a
genuine 4-vc graph. "(2,2,2) excluded in 4-vc" is FALSE. (The n=13 6-reg graph's all-(1,1,4) was
graph-specific, not general.)

THE RECONCILIATION (correct lemma form): v=8 still has min-minority=1, because alongside its (2,2,2)
coloring it ALSO has a (1,2,3) coloring. So the lemma is NOT "(2,2,2) excluded" but "(2,2,2) is never
FORCED — some proper G−v coloring always has a 1-minority." A 'good'/witness vertex needs 2-2-2 in EVERY
coloring; my 2860 forcing-H gadgets achieve that but ONLY non-vertex-critically (the forcing-H + apex
gadget is χ=4 but NOT vertex-critical — apex critical, all 6 neighbors non-critical, verified).

FULL PICTURE: good vertices (2-2-2-forced) exist locally but only NON-vertex-critically; a 4-vc graph CAN
have a vertex with a (2,2,2) coloring but always also has a 1-minority one. The lemma "vc χ=4 ⟹ every
deg-6 vertex has a 1-minority coloring" is the global all-good-CSP-infeasible statement = Dirac k=4.
gallai's triangle-rigidity can't close it because (2,2,2) isn't excluded — it's always ACCOMPANIED by a
1-minority coloring, which is a global fact. This is the SEVENTH angle confirming the irreducible global
wall (adds to §16's six). The deg-6 reduction is correct framing; the SAT (2,2,2)-exclusion test is moot
(answer: not excluded, witness = HCQbfrm).

## 19. Absorber-clique bound is a SMALL-n ARTIFACT (gallai calibration, wall-confirmed)

gallai flagged the "f≥2 ⟹ absorbers form a clique (≤ω≤4)" bound as a likely small-n artifact (it would
resolve Dirac k=4 outright by elementary clique structure — a red flag after 60 years). CONFIRMED from my
n=9,10 data: among f≥2 graphs with ≥2 absorbers, the absorber set is NOT always a clique —
- n=9: 132/132 multi-absorber f≥2 graphs had clique absorber-sets (artifact-consistent at small n).
- n=10: 607 clique BUT 4 NON-CLIQUE (e.g. g6=I?bF`zz~o, absorbers {6,7} non-adjacent), max-absorbers 3.
So non-clique absorber sets appear by n=10. The clique structure is small-n, not a law. gallai's
confirming evidence: Hajós(K4,K4) (n=7, f=1) has 7 absorbers with ω=3 — absorbers freely exceed ω when
f=1. So there is NO intrinsic "absorbers ≤ ω" bound; the f≥2 max-absorber count surely grows with n,
invisibly below the witness regime. 

VERDICT (joint w/ gallai): do NOT build a proof on a bounded/clique absorber set — it's an artifact.
The honest framing is the anti-correlation DIRECTION (f≥2 suppresses absorbers, dense-favorable) +
the exact reduction (witness ⟺ f≥2 ∧ all-absorber), explicitly NOT a provable absorber-count bound.
This is the EIGHTH would-be-lever to collapse (adds to §16's six + §18). The clique-count version dead-ends.
