# E944 — Local Structure of 4-Vertex-Critical Graphs (gallai)

LOCAL structure entry point. All claims below have elementary proofs AND are
computationally verified against the COMPLETE census of 4-vertex-critical graphs
n=4..7 (networkx atlas; same census count/hunter use).

Harness: `gallai_crit.py` (exact χ via SAT, predicates matching the locked Lean defs).
Cross-checked against count/hunter's `critedge.py` and jensen's two-engine harness — identical.

VOCAB: `IsCritical` = VERTEX-critical. A witness (the E944 target) is vertex-critical
with NO critical edge — i.e. a "(4,1)-graph" in Skottová–Steiner notation.

---

## THEOREM 2 (Rainbow-forcing characterization of non-criticality). PROVEN. ★ KEY TOOL

> In a 4-vertex-critical graph G, for any edge uv:
> **uv is non-critical ⟺ in every proper 3-coloring of G−u, the neighbours N(u)∖{v}
> use all 3 colours** ("rainbow-forced from u"). (By symmetry, equivalently from v.)

**Proof.** uv critical ⟺ χ(G−uv)=3 ⟺ G−uv has a proper 3-colouring. Any proper
3-colouring of G−uv restricts to a proper 3-colouring c of G−u in which u's remaining
neighbours N(u)∖{v} occupy ≤2 colours (leaving u a free colour); conversely any proper
3-colouring c of G−u with N(u)∖{v} non-rainbow extends to G−uv by giving u a free colour.
Hence uv critical ⟺ some proper 3-colouring of G−u has N(u)∖{v} non-rainbow ⟺ NOT
rainbow-forced-from-u. Negate. ∎

**Verified:** 103 edges across the full n≤7 census, 0 mismatches with the predicted equivalence.
Generalizes verbatim to k-vertex-critical with k−1 colours.

**INDEPENDENTLY RE-DERIVED (skeptic, 2026-06-10):** from-scratch 3-coloring enumeration + rainbow
test (NOT my code), cross-checked against skeptic's own critical_edges on ALL 141 four-vertex-critical
graphs n≤9: 2303 edges, ZERO mismatches. So Thm 2 is confirmed n≤9 (one-sided test held per edge).
skeptic_gallai_thm_verification.md.

This is the exact local certificate the entry point asked for. It subsumes Theorem 1.

---

## THEOREM 1 (Low-vertex edge criticality). PROVEN. [special case of Thm 2]

> In a 4-vertex-critical graph G, if deg(u)=3 and uv∈E(G) then uv is critical.

**Proof.** N(u)∖{v} has only 2 vertices, so can never use 3 colours; by Theorem 2 (¬rainbow)
uv is critical. (Direct proof: 3-colour G−u, give u a free colour, get a 3-colouring of G−uv.) ∎

**Verified:** 93 (deg-3 u, edge uv) instances, all critical (0 failures).

---

## THEOREM 3 (Witness minimum degree ≥ 6). PROVEN. ★ MAIN RESULT

> An Erdős-944 witness (4-vertex-critical, no critical edge) has **minimum degree ≥ 6**.

**Proof.** Let u be any vertex. Vertex-criticality ⟹ χ(G−u)=3; fix a proper 3-colouring c
of G−u. For every neighbour v, edge uv is non-critical, so by Theorem 2, N(u)∖{v} uses all
3 colours under c. This holding for all v∈N(u) forces (under the single colouring c): every
colour class within N(u) has size ≥2 and all 3 colours appear ⟹ deg(u)=|N(u)| ≥ 3·2 = 6. ∎

**Verified:** the "GOOD ⟹ deg ≥ 6" combinatorial core brute-forced over all 3-colourings of
neighbourhoods of size 1..7: GOOD is satisfiable iff d ≥ 6 (0 counterexamples).

**INDEPENDENT LITERATURE CORROBORATION (decisive).** Skottová–Steiner 2025 (arXiv:2508.08703),
Proposition 5.1, prove min-degree ≥ 3r+3 for any (4,r)-graph; for r=1 that is **min-degree ≥ 6**
— EXACTLY Theorem 3, by a different proof (random-S₃ edge-cut averaging). My route (rainbow-forcing,
Theorem 2) is more elementary and local. Their Problem 5.2 ("Does a 6-regular (4,1)-graph exist?")
confirms 6 is the binding floor: hand to hunter/forge as the primary search target.

### General-k strengthening (k=5 contrast — PROVEN)
The same argument gives δ ≥ **2(k−1)** for a k-vertex-critical witness (k−1 colours, each colour
class ≥2 in N(u)). For k=5: δ ≥ 8 — STRONGER than the paper's k-independent 3r+3 = 6.

**Validation done (3 ways):**
1. Theorem 2 generalizes to k=5: verified on all 5-vertex-critical graphs n≤7 (26 edges, 0 mismatches).
2. The combinatorial core "GOOD ⟹ each of k−1 colours ≥2 in N(u) ⟹ deg ≥ 2(k−1)" brute-forced for
   k=4 (need d≥6) and k=5 (need d≥8): GOOD satisfiable iff d≥2(k−1), 0 counterexamples.
3. k=5 contrast — POSITIVE reality check against THREE actual (5,1)-graphs (built via jensen's
   Jensen/Skottová–Steiner circulant constructor `jensen_code/circulant_analysis.py`, each verified
   χ=5 + vertex-critical + ZERO critical edges):
     - G_{5,2,2}: N=17, δ = 8  ← hits the bound 2(k−1)=8 EXACTLY (sharp!).
     - G_{5,3,2}: N=25, δ = 10.
     - G_{5,2,4}: N=33, δ = 12.
   NOTE: Brown's literal 1992 k=5 graph is unavailable (paywalled, no reproduction; LLM versions
   are hallucinated — jensen). The verified circulant family (build_Gkmq) is the canonical substrate.
   ALL satisfy δ ≥ 8, and the smallest is TIGHT. My theorem does NOT forbid these real witnesses
   (they are dense), and the bound is sharp for k=5. This is the k=5 reality check passing.

So δ ≥ 2(k−1) is a genuinely new strengthening of Skottová–Steiner Prop 5.1 for k≥5, tight-matching
the literature's δ≥6 at k=4. The proof is uniform in k via Theorem 2.

---

## COROLLARY (consequences for the search). PROVEN.

A witness G satisfies (combining Thm 3 with Skottová–Steiner Prop 5.1):
- δ(G) ≥ 6, edge-connectivity ≥ 6; Δ(G) ≤ n−5; n ≥ 11.
- Hence |E(G)| ≥ 3n ≥ 33. The sparsest possible witness is **6-regular** (Problem 5.2).
- Theorem 2 gives an O(1)-per-edge LOCAL non-criticality test usable to prune search:
  for candidate G, an edge uv survives only if N(u)∖{v} is rainbow in every 3-colouring of G−u.

## CENSUS FACT (raw data for wall/count). VERIFIED.
Min # critical edges among 4-vertex-critical graphs: n=4→6, n=6→10, n=7→7. Never 0 (no witness ≤ n=7,
consistent with n≥11 floor). Every non-critical edge in the census is a (4,4)-edge that is
rainbow-forced from both ends (18 such, all at n=7). Degree-3 vertices never sit on a non-critical edge.

---

## THEOREM 4 (Forced-balanced neighborhood rigidity). PROVEN. ★ for impossibility/search

> Let u be a degree-d vertex of a 4-vertex-critical witness. In EVERY proper 3-coloring of G−u,
> the neighborhood N(u) uses all 3 colors with every color class of size ≥ 2. In particular for a
> degree-6 vertex, N(u) is colored EXACTLY 2-2-2 (balanced) in every proper 3-coloring of G−u.

**Proof.** Immediate from Theorem 3's proof: each incident edge non-critical ⟹ every color class in
N(u) has size ≥2 in any fixed 3-coloring c of G−u. For d=6 the only way is 2-2-2. ∎

### Local-structure consequences (necessary conditions on a 6-regular witness)
At every vertex u of a 6-regular witness:
- G[N(u)] contains no K4 (automatic: χ(G)=4) and the 2-2-2 balance is forced under every extension.
- A neighborhood that is 2 disjoint triangles is COMPATIBLE with 2-2-2 (color-permute between them) —
  so it is NOT locally excluded.

**Honest boundary of the local method:** the forced-2-2-2 condition is satisfiable LOCALLY at a single
vertex. Any contradiction for k=4 must come from GLOBAL consistency of forced-2-2-2 across all vertices
simultaneously (a constraint-satisfaction / coloring-rigidity problem), not from a single neighborhood.
This is precisely why the local toolkit constrains the witness sharply but does not by itself resolve
k=4 — and why the problem is open. Handed to wall (impossibility) as the rigid global spec to attack,
and to hunter/forge (search) as the 6-regular target with the rainbow-forcing prune.

## Why this analysis is k=4-specific (per entry-point item 3)
The min-degree bound 2(k−1) and rainbow-forcing characterization hold for all k. What is k=4-SPECIFIC:
- At k=4 the floor δ≥6 is the SAME as Skottová–Steiner's r-bound 3r+3 (r=1) — the bound is tight and
  binding; the sparsest witness is exactly 6-regular (their Problem 5.2). At k≥5 my bound 2(k−1) is
  STRICTLY larger than 3r+3, so the witnesses are forced denser and there is more room — which is why
  Brown/Jensen succeed for k≥5 (verified: G_{5,2,2} has δ=8, hitting 2(k−1) exactly).
- The forced-2-2-2 rigidity uses 3 colors (k−1=3); the small number of colors is what makes the
  global consistency tightest at k=4. With more colors (k≥5) the balanced-partition constraint is
  looser per vertex, leaving the constructive room the literature exploits.

## Deliverable tooling
- `gallai_crit.py`: exact χ (SAT), the three Lean-matching predicates, `is_erdos944_witness`,
  and the Theorem-2 prune `edge_noncritical_local` / `witness_local_prune` (min-deg-6 + rainbow test).

---

## THEOREM 5 (Family-intersection characterization). PROVEN. [bridges local Thm 2 ↔ wall's global decomposition]

> In a 4-vertex-critical G, fix the family {H_e : e non-critical} of spanning edge-critical
> subgraphs (H_e ⊆ G−e minimal 4-chromatic). An edge f is **critical ⟺ f ∈ E(H_e) for every
> member H_e** (equivalently f lies in every spanning 4-chromatic subgraph). Hence:
> **G is a witness ⟺ ⋂_e E(H_e) = ∅** (no edge is common to all members).

**Verified:** on all n=7 4-vertex-critical graphs, "f critical ⟺ f in every H_e" holds (0 mismatches).
On C7-complement (14 edges, 7 critical) the multiplicity mult(f)=#{e : f∈H_e} is EXACTLY |family|=7
for every critical edge and < 7 (avg 4) for every non-critical edge — a clean separator.

This is the same object as wall §1.4 (⋂ over spanning 4-chromatic subgraphs), reached from the
family side, and it ties to Theorem 2: f critical (local: ¬rainbow-forced) ⟺ f in every H_e (global).

### Verdict on the H_e-family OVERLAP lever for a witness (per team-lead's pointer)
- **Edge-count overlap is VACUOUS for a dense witness.** KY gives e(H_e) ≥ (5n−2)/3 ≈ 1.67n, but my
  Thm 3 forces e(G) ≥ 3n, so L_e ≥ 4n − 2e(H_e) goes negative — the Gallai-forest count yields nothing
  (this is exactly wall's pre-registered obstruction #1: KY is a LOWER bound, no upper bound on e(G)).
- **The "degree-3-in-G ⟹ simultaneous Gallai-forest vertex" lever is EMPTY for a witness.** Thm 3 says
  a witness has NO degree-3 vertices, so that specific simultaneous-membership constraint never fires.
- **What survives:** Thm 5 (family-intersection = ∅) + Thm 4 (per-vertex forced 2-2-2). The real
  obstruction, if any, is GLOBAL coloring-rigidity (a CSP across all vertices), not edge-count overlap.

---

## KY DENSITY BRIDGE — vocab-warning correction (per team-lead). VERIFIED.

The earlier VOCAB WARNING was slightly over-broad: the **density half** of the edge-critical toolkit
DOES transfer to the (vertex-critical) target, only the **structural half** doesn't.

**Bridge (one line, verified):** if G is vertex-critical with χ=4 and H ⊆ G is any minimal 4-chromatic
subgraph, then H is edge-critical AND spanning (if v ∉ V(H) then H ⊆ G−v ⟹ χ(G−v) ≥ 4, contradicting
vertex-criticality). So Kostochka–Yancey binds H on the SAME vertex count: **e(G) ≥ e(H) ≥ (5n−2)/3.**
Verified on the full n≤7 census (0 violations). [Infinite-V caveat handled by skeptic's statement-lock:
a witness has finitely many edges hence is finite, so n is a genuine finite integer here.]

- What transfers: KY/Ore DENSITY lower bounds (via the spanning edge-critical H). But for THIS object
  the KY floor (5n−2)/3 is SUPERSEDED by Theorem 3's e(G) ≥ 3n — so KY adds nothing beyond min-deg-6.
- What does NOT transfer: Gallai's low-vertex FOREST theorem applies to each H_e ⊆ G−e, not to G — G's
  degree-3 vertices (none, for a witness) need not be H_e's degree-3 vertices.

## DENSITY REMARK (redirects count's upper-bound hunt). VERIFIED.
The target CAN be dense, and the known k≥5 witnesses ARE dense: the Jensen circulants I built have
e(G)/n = 4, 5, 6 (degrees 8, 10, 12) — well above any critical-graph floor. There is NO non-trivial
upper bound on e(G) for a vertex-critical-no-critical-edge graph (adding edges preserves χ=4 and can
preserve vertex-criticality). So an upper-bound/density-ceiling hunt on e(G) will NOT close — the
witness is constrained from BELOW (δ≥6, e≥3n) and by coloring-rigidity, not from above.

---

## THEOREM 6 (Jensen–Siggers E* structure — empirical confirmation + local explanation). VERIFIED.

Jensen–Siggers 2012 conjecture: if Dirac k=4 is false, the critical-edge set E*(G) of a 4-vertex-critical
graph may be forced CONNECTED and even SPANNING. I tested this on the EXHAUSTIVE census of 4-vertex-critical
graphs and connected it to my local certificate.

**Empirical result (CORRECTED by skeptic n≤10 dual-checker census):** E* is exception-free NONEMPTY and
SPANNING (touches every vertex) for EVERY 4-vertex-critical graph through n=10. The stronger "E*
CONNECTED" form is **REFUTED at n=10** — 3 graphs have a disconnected (2-component) but still spanning
E* (g6: ICpdbY{]_, ICpddxy^?, ICpdlps]_). So a minimal-counterexample / global-CSP argument may rely on
"E* nonempty" and "E* spanning" but NOT on "E* connected." (My earlier n≤8 connected observation was
a small-n artifact; skeptic_jensen_siggers_Estar.md is the authoritative census.)

**Local explanation via Theorem 2/4 (the bridge to my work):**
- E* spanning ⟺ every vertex has ≥1 critical incident edge ⟺ NO vertex is "good" (all-incident-non-critical).
- By Theorem 4, a "good" vertex needs degree ≥6 with a forced-2-2-2-balanced neighborhood. A WITNESS is
  exactly the all-vertices-good graph (E* = ∅). So "E* spanning" and "witness (E*=∅)" are the two extremes;
  the Jensen–Siggers conjecture is that you cannot have PARTIAL goodness with a disconnected/non-spanning E*.
- The Jensen–Siggers B-core K_{2m,2m,2m} has ZERO critical edges — and this is EXACTLY the rainbow-forcing
  mechanism of Theorem 2 over-satisfied: each vertex's neighborhood spans both other color classes with
  ≥2m ≥2 vertices each, so deleting any single neighbor never frees a color. VERIFIED: K_{2,2,2}, K_{4,4,4},
  K_{6,6,6} all have 0 critical edges. The B-core achieves rainbow-forcing trivially BECAUSE it is dense and
  balanced — but it is only 3-chromatic.

**The k=4 bottleneck, in local terms (synthesis):** to lift the (critical-edge-free) balanced B-core to a
4-CHROMATIC vertex-critical graph, Jensen–Siggers must add the "color-disagreement transfer" gadget G(m).
That gadget is precisely where rainbow-forcing FAILS — it produces the residual Θ(n) critical edges (their
E*). So the open k=4 question, in my language, is: **can one force χ=4 while keeping every vertex's
neighborhood rainbow-forced (Theorem 4's 2-2-2 condition) everywhere?** The B-core shows balanced-rainbow
is easy at χ=3; the obstruction is making it coexist with χ=4. This is the same global coloring-rigidity
wall identified, now with a concrete mechanism (the disagreement gadget) marking where it breaks.

**Handoffs:** to forge — the sharp constructive target is to redesign the G(m) disagreement gadget so its
edges also become rainbow-forced (Theorem 2 test) without collapsing χ to 3. To wall/skeptic — the
impossibility lemma to target is exactly Jensen–Siggers's "E* connected/spanning of positive size always",
which my census confirms through n=8; a proof that E* spanning is FORCED (no good vertex can exist) would
refute Dirac k=4. My Theorem 4 reduces "no good vertex" to "no vertex has a forced-2-2-2 neighborhood".
