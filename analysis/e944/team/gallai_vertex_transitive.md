# E944 — The vertex-transitive theorem (gallai, proof-team)

TARGET: "No vertex-transitive graph is a (4,1)-witness" (no vertex-transitive 4-vertex-critical graph
with zero critical edges). If proven, rigorously closes the entire symmetric search space.

## MAKE-OR-BREAK (settled): the theorem is k=4-ONLY.
Jensen's k=5 witnesses ARE circulants (vertex-transitive). Verified: G_{5,2,2} (circulant on Z₁₇) is a
genuine (5,1)-witness — χ=5, vertex-critical, ZERO critical edges, cyclic shift is an automorphism. So
"no vertex-transitive (k,1)-witness" is FALSE at k=5. The theorem is k=4-only; any proof MUST use the
3-color (q=3) structure. (The triangle rainbow-rigidity 1,1,1/2,2,2 forced at ℤ₃, failing at ℤ₄, is the
only q=3-specific lever established — but triangle PRESENCE alone is not the discriminator; both
k=4-vertex-critical circulants and the k=5 witness contain triangles.)

## EMPIRICAL BASE (strong).
Exhaustive over circulants C_n(D): among 137 four-VERTEX-CRITICAL circulants n≤24, ZERO are witnesses —
every one has ≥7 critical edges. (Earlier 7/36 figure was diluted by non-vertex-critical 4-chromatic
circulants, which are irrelevant.) Each vertex-critical circulant has exactly the critical edges of ONE
distance-orbit (e.g. C₇(1,2): distance-1 critical, 7 critical edges). Consistent with count's 610
circulants + skeptic's n=31 confirmations + non-abelian Cayley sweeps.

## CLEAN REDUCTION (the V-T-specific simplification).
By the orbit lemma, edge-criticality is constant on Aut edge-orbits. By vertex-transitivity, all
vertices are Aut-equivalent (one vertex-orbit), so the "good/absorber" condition (my Theorem 4 /
forge's cnt(v)) is IDENTICAL at every vertex. Hence:
  witness ⟺ f(G)≥2 AND every vertex an absorber ⟺ (by symmetry) f(G)≥2 AND the single vertex-orbit
  is an absorber.
forge's localization B₁ = ½ Σ_v cnt(v) becomes **B₁ = (n/2)·cnt(v₀)** under vertex-transitivity, so
the theorem reduces to a SINGLE per-vertex condition: "cnt(v₀)=0 is impossible for a vertex-transitive
4-vertex-critical graph." This is the cleanest reduction available for the V-T case.

## CRITICAL CAVEAT (wall + my Round 2): vertex-criticality is ESSENTIAL.
The double-root / f≥2 / B₁=0 condition occurs for 15 NON-vertex-critical 4-chromatic graphs at n=7. So
the proof MUST invoke vertex-criticality as a live hypothesis throughout, not just χ=4. The content is
how vertex-criticality + vertex-transitivity + q=3 interact to force cnt(v₀)>0.

## HONEST STATUS: NO PROOF YET. Where it stands and why it's hard.
- The reduction is clean (single per-vertex condition under symmetry) but does NOT escape the global
  3-coloring CSP — vertex-transitivity makes the absorber condition UNIFORM, not LOCAL. "cnt(v₀)=0"
  still quantifies over all 3-colorings of G−v₀, a global object.
- The q=3 pigeonhole lever (forge): at a degree-d vertex, d≥6 neighbors split into 3 color classes;
  cnt(v)=0 needs every class ≥2 in every 3-coloring of G−v. The pigeonhole "3 classes over ≥6
  neighbors can't all balance" is the hoped gap — but it does NOT bite per-coloring (2-2-2 IS
  achievable for a single coloring; the k=5 witness achieves 2-2-2-2 at q=4). The gap would need to
  use a GLOBAL count over all colorings, where I keep hitting the same circularity (= Theorem 4).
- ASSESSMENT: the theorem is very likely TRUE (strong empirical base, k=4-specific) but its proof
  appears to require the SAME global-CSP traction that Dirac k=4 itself needs, restricted to symmetric
  graphs. Vertex-transitivity simplifies the bookkeeping (one orbit) but not the core difficulty. I
  did NOT find a symmetry-specific shortcut (Burnside/averaging on near-colorings did not force B₁>0).
- The one un-tried symmetry angle: a representation-theoretic / character-sum argument on the Aut-action
  over the near-3-coloring space (distinct from the ℤ₃-Fourier I killed in INVENTIONS G-INV-5, which
  was over colors not over Aut). Recorded as the open lever; needs rep-theory tools.

## VERDICT
Reduced the V-T theorem to a single symmetric per-vertex condition (cnt(v₀)=0 impossible) with a strong
empirical base, settled its k=4-specificity, and identified the q=3 pigeonhole + Aut-character angles.
But no proof: the symmetric case inherits the global-CSP core. Honest residue: the reduction + the
make-or-break k=4-only determination + the empirical closure of the circulant space (137 vertex-critical
circulants, 0 witnesses, n≤24). A genuine proof needs a symmetry-specific obstruction I could not find.

## REP-THEORY ATTEMPT (timeboxed, DEAD — 2026-06-10)
Team-lead-approved single attempt: decompose the near-coloring space as an Aut(G)-module; cnt(v₀) is
the trivial-rep multiplicity (up to normalization); ask if 4-vertex-criticality forces it >0.
RESULT: cnt(v₀)>0 ⟺ some 3-coloring of G−v₀ gives N(v₀) a SINGLETON color class. Witness (δ≥6) needs
this to FAIL everywhere = every 3-coloring balances N(v₀) ≥2 per class = EXACTLY Theorem 4. The
Burnside/character route ⟨perm char, triv⟩=(1/|Stab|)Σ_g Fix(g) needs Fix(identity)=#near-colorings>0,
which is the very thing to show — CIRCULAR. And it does NOT distinguish q=3 from q=4 (both allow
balanced no-singleton partitions per coloring), so no q=3-specific lever. DEAD: same global-CSP core.
(Concrete check: C₇(1,2), deg-4 case, N(0) partitions {1,2,1} with a singleton ⟹ cnt(0)>0 ⟹ critical
edge — but this is the easy δ=4 case; the δ≥6 balanced case is where it reduces to Theorem 4.)
