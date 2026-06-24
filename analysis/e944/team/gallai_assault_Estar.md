# E944 ASSAULT — attempt to prove E* ≠ ∅ at k=4 (would resolve Dirac k=4 = NO)

**Owner:** gallai. **Order:** team-lead ASSAULT MODE. **Verdict: proof does NOT go through; exact death
point isolated below.** All steps reality-checked against verified k=5 (5,1)-witnesses (G_{5,2,2} on
Z₁₇, δ=8, zero critical edges) — every lemma I use MUST hold at k=5, and the contradiction MUST be
k=4-specific. That discipline is what kills each route.

## Target
Prove: every 4-vertex-critical graph has a critical edge (E* ≠ ∅). Equivalently: no (4,1)-graph exists.
This resolves Dirac k=4 negatively.

## Weapons (all proven, see gallai_local_structure.md)
- Thm 3/4: a witness has δ ≥ 6; at every degree-6 vertex u, in EVERY 3-coloring of G−u, N(u) is
  forced 2-2-2 balanced.
- Thm 2: edge uv critical ⟺ in some 3-coloring of G−u, N(u)∖{v} is non-rainbow (a neighbor v is the
  unique one of its color).
- Thm 5: f critical ⟺ f in every spanning 4-chromatic subgraph.
- skeptic/census: E* NONEMPTY + SPANNING on ALL 4-vertex-critical graphs n ≤ 10 (dual-checker, 0
  exceptions). "E* connected" REFUTED at n=10. Strong empirical signal that E* ≠ ∅ and E* spanning are TRUE;
  any minimal-counterexample argument may use nonempty+spanning but NOT connected.

## Route 1 — Edge-counting / Kostochka–Yancey density / potential method. DIES (vacuous).
KY density and the potential method are sparsity LOWER bounds (e(H) ≥ (5n−2)/3 for edge-critical H).
The witness is DENSE: my Thm 3 forces e(G) ≥ 3n, and the known k≥5 witnesses have e/n = 4,5,6. A lower
bound cannot contradict a dense object — there is no matching upper bound on e(G) for vertex-critical
graphs. **= wall's pre-registered obstruction #1.** Every counting/potential tool fails identically.

## Route 2 — Kempe-chain pair-separation. DIES (necessary but never fires).
I derived a genuine **Kempe-rigidity lemma** (NECESSARY for any witness, verified 0 violations on the
k=5 witness): for every vertex u, every 3-coloring c of G−u, and every pair x,y of same-colored
neighbors of u, x and y must lie in the same Kempe (2-color) component for every relevant color pair —
else a Kempe swap frees a color for u, giving a proper 3-coloring of G, contradicting χ=4.

Death: I tested whether 4-vertex-critical graphs always CONTAIN a Kempe-separable same-color neighbor
pair (which would force a critical edge). On all 8 four-vertex-critical graphs at n=8: **0 had a
separable pair** in the sampled 3-coloring. Reason (diagnosed): k=4 criticality comes from a SINGLE
neighbor being color-isolated (Thm 2 mechanism: v unique of its color ⟹ u takes that color in G−uv),
NOT from separating a pair. The pair-separation lemma is strictly stronger than the actual mechanism,
so it never fires. The single-neighbor-isolation it reduces to is the negation of Thm 4's balance — and
that balance IS satisfiable (k=5 witness achieves the 2-2-2-2 analogue). No k=4 contradiction.

## Route 3 — Local 2-2-2 rigidity as a global CSP. DIES locally, survives only globally.
The witness condition = "every vertex good" = at every u, every 3-coloring of G−u has N(u) balanced
(no color-isolated neighbor). This is the forced-2-2-2 CSP. Reality check: the k=5 witness satisfies
the 4-color analogue (2-2-2-2) at every vertex (verified by SAT: no 4-coloring of G−u leaves N(u)
using ≤3 colors). So the balance condition is **per-vertex and per-coloring SATISFIABLE**. The neighborhood
graph G[N(u)] in the k=5 witness even has χ=3 (doesn't structurally need all colors) — the balance is
enforced GLOBALLY, not locally. No local certificate forbids it.

## DEATH POINT (the deliverable)
All three independent routes die at the SAME wall: **the only obstruction left is the JOINT
satisfiability of forced-balance across ALL vertices AND all 3-colorings simultaneously — an
irreducibly global 3-coloring constraint-satisfaction problem.** It does NOT decompose into any local,
edge-counting, potential, or Kempe-swap certificate. Every such certificate is either vacuous (dense
witness) or satisfiable (k=5 reality check). The k=4-vs-k=5 distinction (3 vs 4 colors) lives ENTIRELY
inside this global CSP and nowhere in the reducible structure. This is exactly the 1970-open core.

### What this says about the witness (spec for the builders)
A witness must thread an irreducibly global needle: a dense (δ≥6, e≥3n), ASYMMETRIC (forge: vertex-
transitive is k=4-specifically forbidden; even if proven only rules out symmetric graphs) graph whose
EVERY vertex-deleted 3-coloring balances EVERY neighborhood — with no local, counting, or symmetry
structure available to enforce it. The Jensen–Siggers near-miss shows balance is achievable on a dense
B-core (K_{2m,2m,2m}, zero critical edges via over-satisfied rainbow-forcing) but the χ=4-forcing
gadget G(m) re-introduces Θ(n) color-isolated neighbors (the residual E*). The open question, sharply:
can the χ=4 forcing be done WITHOUT any color-isolated neighbor anywhere? No tool we have answers it.

## Honest status
Proof FAILED (as expected for a 1970-open problem). The value delivered is the death point: a rigorous
demonstration that E*≠∅ at k=4 cannot follow from any local/counting/Kempe/potential argument — it is
equivalent to the global 3-coloring CSP. This tells wall NOT to keep pushing reducible certificates,
and tells the builders the exact (irreducibly global, asymmetric, balance-everywhere) spec to target.

---

## Route 4 — ℤ₃-tension / flow obstruction (pairing with wall). PROMISING but DOES NOT YET BITE.

wall proposed the one genuinely-unexplored k=4-specific lever: a ℤ₃-tension/nowhere-zero-flow
obstruction (ℤ₃ is special at 3 colours; would auto-pass the k=5 reality check since ℤ₄ flows differ).

**Formulation (clean):** a proper 3-colouring ⟺ a nowhere-zero ℤ₃-tension (the coboundary of the
colour potential). So χ(G) ≥ 4 ⟺ G has NO nowhere-zero ℤ₃-tension; edge uv is critical ⟺ G has a
ℤ₃-tension that is nonzero everywhere except possibly on uv; and **G is a witness ⟺ G has no
ℤ₃-tension that vanishes on ≤1 edge, and χ=4.**

**The genuinely ℤ₃-specific rigidity (passes k=5 check):** around any cycle a tension sums to 0 (mod 3).
On a TRIANGLE, all-nonzero forces values 1,1,1 or 2,2,2 (since 1+1−1=1≠0) — i.e. the triangle is
RAINBOW-rigid. This is exactly why 3 colours are tight, and it FAILS at ℤ₄ (a triangle admits
1+1+2=0 mod 4, not rainbow-forced). So any obstruction built on triangle-rainbow-rigidity is
automatically k=4-specific. [But note: the k=5 witnesses DO contain triangles, so triangle-richness
alone is not the obstruction — the rigidity must be used globally.]

**Why it does not yet bite (honest):**
- ℤ₃-tension ⟺ 3-colouring is a RESTATEMENT, not new leverage by itself. χ≥4 = "no nowhere-zero
  ℤ₃-tension" is the definition.
- The tool that would give traction — tension/flow DUALITY (Tutte) — needs PLANARITY. The witness is
  dense and non-planar (δ≥6, e≥3n), so there is no flow-dual graph and no 3-flow-conjecture-style
  obstruction transfers.
- Deletion–contraction restates it again: with P(G,3)=0, P(G−e,3)=P(G/e,3), so uv critical ⟺
  P(G/e,3)>0 (a 3-colouring identifying u,v). Witness ⟺ P(G/e,3)=0 for every edge. Verified the
  mechanism on n=8 (some edge always has P(G/e,3)>0), but "is some P(G/e,3)>0 FORCED by χ=4 + vertex-
  critical?" is precisely Dirac k=4 restated — no free forcing.

**What would make it bite (the open sub-target):** a counting or cohomological identity tying the
number of "almost-nowhere-zero ℤ₃-tensions" (vanishing on ≤1 edge) to a non-vanishing invariant of a
χ=4 vertex-critical graph — something that does NOT rely on planar duality and that uses the triangle
rigidity globally. Neither wall nor I could produce it. This is the single most promising unexplored
direction precisely because it is the only one that is intrinsically k=4-specific rather than vacuous
or k-independent. Recorded as the recommended next lever (also in gallai_HANDOFF.md).

---

## Route 5 — ZERO-FREE-REGION / chromatic-root-structure near x=3. DEAD (disconnect proven).

Team-lead's proof-team assignment: bound Σ_e P(G−e,3) = B₁ via the root structure of P(G,x) NEAR x=3
(the analytic version; distinct from G-INV-8's killed AT-x=3 multiplicity). archivist supplied
Sokal/Jackson zero-free-region mechanics. Reality-checked at k=5 throughout.

### What I tested
1. Complex chromatic roots of 4-vertex-critical graphs near x=3: x=3 is always a root (4-chromatic);
   nearest OTHER root sits at distance 0.5–1.0. Computable analytic terrain, genuinely new.
2. Candidate theorem: x=3 is always a SIMPLE root of P(G,x) for a 4-vertex-critical graph (P'(3)≠0).
   VERIFIED 0 multiple-root cases across all 15 four-vertex-critical graphs n≤8. Clean — BUT see below.

### The death point (a hard DISCONNECT, proven)
The zero-free lever requires the analytic root data near x=3 to control B₁ = Σ_e P(G−e,3). IT DOES NOT.
Discriminating test on the 15 B₁=0 (min_mono≥2) graphs at n=7: **6 of them have x=3 as a SIMPLE root**
(P'(3)≠0) while B₁=0. Explicit: FQyvw, FUZvw, FUxvw, FUzvw all have P(3)=0, **P'(3)=−6 (simple root,
nonzero)**, yet **B₁=0**. So "x=3 simple root" / "P'(3)≠0" — exactly the quantity a zero-free region
around 3 controls — COEXISTS with B₁=0. The analytic root structure at/near x=3 does NOT determine B₁.

**Why (root cause, makes the death structural not incidental):** B₁ = Σ_e P(G−e,3) is a POSITIVE
combinatorial count — each P(G−e,3) ≥ 0 counts proper 3-colorings of G−e, so B₁ ≥ 0 with B₁=0 iff every
term is 0. But P'(G,3) (and any analytic functional of P's roots) is a SIGNED, alternating sum of
chromatic coefficients. Sign cancellation severs the link: P can have a clean simple root at 3 (its
derivative nonzero) while the positive count B₁ vanishes. A zero-free DISC around 3 bounds |P| and its
derivatives there, i.e. controls the SIGNED polynomial — which is the wrong object. No zero-free-region
theorem can lower-bound a positive coloring-count that is invisible to the signed analytic data.

### STRONGEST kill (proven): B₁ is NOT a function of P(G,x) at all.
Beyond sign cancellation, a definitive impossibility for the whole lever: I found CHROMATICALLY-
EQUIVALENT graphs (identical chromatic polynomial P(G,x)) with DIFFERENT B₁ (e.g. n=7: F?bnw has
B₁=108, F?qnw has B₁=96, SAME P(G,x)). So B₁ is provably NOT a function of P(G,x). Therefore NO
approach using only the analytic structure of the single polynomial P(G,x) — zero-free region,
contour integral, root locations, ANY analytic functional of P(G,x) — can determine or lower-bound
B₁. Reason: B₁ = Σ_e P(G−e,3) is a sum over the VALUES of the n_edges DIFFERENT polynomials
P(G−e,x); a zero-free region of P(G,x) says nothing about the values of the OTHER polynomials
P(G−e,3). The lever is dead at the strongest possible level.

### Verdict
The zero-free / chromatic-root lever is DEAD, and the death is structural: the target B₁ is a positive
count not expressible through the root structure of P(G,x) near x=3 (sign cancellation). This kills the
LAST analytic lever identified in the invention-blitz saturation map. Combined with R1–R4 + the f-cocycle
dig (all reduce to Theorem 4 = "every vertex good"), the impossibility direction's honest residue is:
**E*≠∅ at k=4 is exactly equivalent to the global "every vertex good" CSP (Theorem 4), and is provably
NOT reducible to (a) any edge-count/density bound [vacuous, witness dense], (b) any Kempe-swap
certificate [single-neighbor mechanism, satisfiable at k=5], (c) the ℤ₃ Potts/cocycle simple-root or
absorber reformulations [equivalent restatements], or (d) any chromatic-root / zero-free-region bound
near x=3 [signed-vs-positive disconnect].** This is the publishable saturation map of the impossibility
direction. k=5 reality check holds throughout (every reduced statement is realizable at q=4).
