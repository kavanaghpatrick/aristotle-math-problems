# forge — Structural theorem: degree-3 vertices force critical edges (E944, k=4)

Standalone statement of the cleanest proven result from the forge construction
assault. Self-contained, elementary, exact-verified. Candidate for Lean
formalization and for the impossibility-direction toolkit.

## Definitions (locked, FormalConjecturesForMathlib/.../Coloring.lean)
- G is **4-vertex-critical**: χ(G)=4 and for every vertex v, χ(G−v) < 4.
- edge e is **critical**: χ(G−e) < 4 (i.e. = 3, since removing an edge drops χ by ≤1).
- A **(4,1)-witness** (Erdős-944 k=4,r=1) is a 4-vertex-critical graph with NO
  critical edge.

## Per-vertex criticality lemma
> **Lemma.** For a vertex v of a 4-vertex-critical graph G:
> v is incident to a critical edge  ⟺  there is a proper 3-coloring of G−v under
> which some color appears EXACTLY ONCE among the neighbors N(v).
>
> Proof.
> (⇐) Suppose 3-coloring c of G−v has color a appearing once in N(v), at the
>     unique neighbor u with c(u)=a. Delete edge vu. In G−vu the neighbors of v
>     have colors ⊆ {the other two colors}, so set c(v)=a: a proper 3-coloring of
>     G−vu. Hence χ(G−vu)=3 and vu is critical.
> (⇒) Suppose vu is critical, witnessed by a 3-coloring c′ of G−vu with c′(v)=a.
>     The only edge of G missing from G−vu is vu, so c′ is proper on G except
>     possibly across vu; since c′ is proper on G−vu and v has color a, every
>     neighbor w≠u of v has c′(w)≠a. Restricting c′ to G−v is a proper 3-coloring
>     in which color a appears in N(v) only possibly at u — and it must appear (v
>     could not take a free color, as χ(G)=4 means c′ cannot extend v's coloring
>     to all of G), so exactly once, at u. ∎

This lemma is the exact negation, per vertex, of wall's witness criterion
("every color appears ≥2× in N(v) in every 3-coloring of G−v"). So:
**"every vertex incident to a critical edge" ⟺ "G is not a (4,1)-witness".**
(Hence the global vertex-spanning fact is a reformulation of the open problem,
not an independent lemma — stated honestly.)

## Main theorem (NEW, clean corollary)
> **Theorem.** If a vertex v has degree exactly 3 in a 4-vertex-critical graph G,
> then ALL THREE edges incident to v are critical.
>
> Proof. v is critical, so χ(G−v)=3; fix any proper 3-coloring c of G−v. If two
> neighbors of v shared a color, only ≤2 colors appear in N(v), leaving a free
> color for v and extending c to a proper 3-coloring of G — contradicting χ(G)=4.
> So the 3 neighbors of v receive 3 distinct colors: each color appears exactly
> once in N(v). By the Lemma (⇐), each of the 3 edges at v is critical. ∎
>
> **Corollary.** A (4,1)-witness has minimum degree ≥ 4 — it contains no vertex
> of degree 3.

## Exact verification
- Theorem ("deg-3 ⟹ all 3 edges critical"): TRUE for every 4-vertex-critical
  graph on n=7 (7 graphs), n=8 (8), n=9 (124) — 0 exceptions.
- Corollary base: no (4,1)-witness on n≤10 (exhaustive), all have a critical edge;
  and the unique 6-regular near-miss C₁₃(1,2,5) has δ=6 but still a critical orbit.
- On Jensen–Siggers H(m=3) (n=67, |E*|=90): ALL 90 critical edges touch a degree-3
  vertex (90/90); 44 of 67 vertices have degree 3. The theorem exactly accounts
  for why the J-S gadget's critical-edge set is unavoidable and spanning.
- Negative refinement: the stronger "every vertex incident to ≥2 critical edges"
  is FALSE (counterexample: 4-vertex-critical graph `HCp\`fr]` on n=9 has a vertex
  of critical-degree exactly 1). The per-vertex bound is tight at 1.

## Relation to known results
- Weaker, self-contained cousin of Skottová–Steiner Prop 5.1 (which proves the
  stronger δ≥6, edge-connectivity ≥6, |V|≥11 for a witness). Our δ≥4 needs only
  the elementary lemma above — useful as a Lean-friendly first step and as the
  conceptual "why" behind the degree lower bound.
- Explains Jensen–Siggers' own remark that their critical-edge set E* is
  connected and spanning: the construction is forced to use degree-3 transfer
  vertices, each of which (by the Theorem) contributes 3 critical edges.

## δ≥6 generalization (wall, gallai Thm 3 = SkSt Prop 5.1) — my deg-3 thm is the base case
wall confirmed my deg-3 theorem is correct + independently matches gallai Thm 1 / wall §2.3.
The FULL witness degree bound is δ≥6, not just δ≥4, and my theorem is its BASE CASE:
- My deg-3 theorem: a deg-3 vertex forces each of 3 colors to appear EXACTLY ONCE in N(v)
  (3 neighbors, 3 distinct colors) ⟹ each is a singleton ⟹ 3 critical edges ⟹ δ≥4.
- ITERATED (gallai Thm 3): a witness needs each color to appear ≥2 TIMES in N(v) under every
  3-coloring of G−v (the 2-2-2 BALANCE). With 3 colors each ≥2, deg(v) ≥ 6. So δ≥6, and
  6-regular is the sparsest candidate (SkSt open Problem 5.2).
- The TIGHT per-vertex witness criterion (wall, validated): vertex v is GOOD (no incident
  critical edge) ⟺ every color appears ≥2 in N(v) under every 3-coloring of G−v. My
  "every vertex ≥2 critical edges is FALSE (n=9 cex)" confirms it's this tight ≥2-balance
  criterion, NOT a uniform critical-edge count.
So for the impossibility proof: the open core is exactly "can EVERY vertex of a δ≥6 4vc graph be
2-2-2-balanced (good) simultaneously?" — gallai's Thm 4 tightness / the q=3 zero-free lever. My
deg-3 theorem closes the δ<6 case (any low-degree vertex is automatically bad ⟹ critical edge);
the proof's remaining work is purely the 6-regular/2-2-2 regime where G_5,2,2 (δ=8) is the k=5 escape.
