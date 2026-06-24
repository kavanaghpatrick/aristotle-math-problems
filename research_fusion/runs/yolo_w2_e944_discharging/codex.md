Reading additional input from stdin...
OpenAI Codex v0.130.0
--------
workdir: /Users/patrickkavanagh/math
model: gpt-5.5
provider: openai
approval: never
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019e7923-58dc-75a1-859a-7ee18adffb66
--------
user
Erdős 944, Dirac k=4 case (4-vertex-critical graphs, no critical edge). Brown 1992 (k=5), Lattanzio 2002 (k-1 non-prime), Jensen 2002 (k>=5). k=4 OPEN. Martinsson-Steiner arXiv:2508.08703.

ANGLE: DISCHARGING METHOD (Appel-Haken 1976, Robertson-Sanders-Seymour-Thomas 1997 J. Combin. Theory B 70, Cranston-Rabern 2015 "List-Coloring with Discharging"). Transplant to Dirac k=4 with G a hypothetical 4-vertex-critical graph with no critical edge.

(a) Initial charge c(v) = d(v) - 4. Sum = 2|E| - 4|V|. By Gallai 1963 the degree-3 vertices induce K_4s and odd cycles. By minimum-degree-from-criticality d(v) >= 3 (4-critical). Kostochka-Stiebitz 1999 gives |E| >= (k/2 + (k-3)/(k^2-2k-1))|V|, so for k=4 we get |E| >= (2 + 1/7)|V| hence sum of charges >= 2|V|/7.

(b) Discharging rules to redistribute charge from high-degree positive vertices to negative-charge degree-3 vertices. Need rules R1, R2, R3 specific to no-critical-edge condition: every edge e in G has chi(G-e) = chi(G) = 4 so G-e is 4-chromatic, i.e. for every edge uv there exists a 3-coloring of G-uv after some vertex removal — wait, no: edge e is non-critical means chi(G - e) = chi(G) = 4 still; so G is edge-NON-critical. The no-critical-edge condition is strong: every edge can be removed without dropping chromatic. Therefore for every uv in E(G), the graph G - uv is still 4-chromatic. This gives a structural propagation rule.

(c) Reducible configurations from Cranston-Rabern 2015 and similar: (i) two adjacent degree-3 vertices, (ii) degree-3 vertex with two degree-3 neighbors (3-path), (iii) the unique non-Brown configuration where a K_4-component of G_3 is bridged to the rest by exactly one edge.

(d) Honest assessment: can discharging close k=4 Dirac?

QUESTION: Fill in (a)(b)(c)(d) with 800-1200 words total. Be specific: name 3-5 discharging rules with rationale, 3-5 reducible configurations specific to no-critical-edge, and give an honest evaluation whether discharging alone can close k=4 or only narrow the search to a finite case-analysis. Cite Robertson-Sanders-Seymour-Thomas 1997, Cranston-Rabern 2015, Kostochka-Stiebitz 1999.
codex
I’ll check the current bibliographic/status details before giving the synthesis, since this is a live open-problem area and you asked for specific citations.
web search: 
web search: Martinsson Steiner arXiv 2508.08703 Dirac k=4 critical edge 4-critical graph
web search: 
web search: https://arxiv.org/abs/2508.08703
web search: 
web search: Robertson Sanders Seymour Thomas 1997 J Combinatorial Theory B 70 four colour theorem discharging unavoidable reducible
web search: 
web search: "List-Coloring with Discharging" Cranston Rabern 2015
web search: 
web search: site:cranston.servehttp.com "List-Coloring" "Discharging" Rabern
web search: 
web search: Kostochka Stiebitz lower bound number of edges colour-critical graphs vertex-critical
codex
The transplant as stated breaks at a basic point: in a 4-vertex-critical graph with no critical edge, there are no degree-3 vertices at all. In fact there are no degree-4 or degree-5 vertices either.

Let \(G\) be 4-vertex-critical and suppose \(uv\in E(G)\). Since \(G-v\) is 3-colorable, take a 3-coloring \(\phi\) of \(G-v\). If \(\phi(u)\) is the unique occurrence of its color on \(N(v)\), then \(\phi\) extends to a 3-coloring of \(G-uv\) by giving \(v\) the color \(\phi(u)\). Hence \(uv\) is critical. Therefore, in a graph with no critical edge, for every \(v\), every 3-coloring of \(G-v\) must color \(N(v)\) so that each of the three colors appears at least twice. Thus

\[
d(v)\ge 6 \quad \text{for every }v.
\]

So the degree-3 discharging picture is vacuous. Gallai’s low-vertex structure is useful for ordinary critical graphs, but here the no-critical-edge hypothesis kills the whole low-degree layer before discharging begins.

For (a): with \(c(v)=d(v)-4\),

\[
\sum_v c(v)=2|E|-4|V|.
\]

The Kostochka-Stiebitz bound gives \( |E|\ge (2+1/7)|V|\) for a spanning 4-critical subgraph, hence \(\sum c(v)\ge 2|V|/7\). But the no-critical-edge condition gives the stronger \(\delta(G)\ge 6\), so actually \(|E|\ge 3|V|\) and \(\sum c(v)\ge 2|V|\). There is no negative charge to absorb.

For (b), the correct propagation rule is not “send charge to 3-vertices”; it is:

1. **Singleton-color rule.** If some 3-coloring of \(G-v\) gives a neighbor \(u\) a color unique on \(N(v)\), then \(uv\) is critical. Forbidden.

2. **Neighbor-pairing rule.** If \(d(v)=6\), then in every 3-coloring of \(G-v\), the six neighbors of \(v\) must split exactly into three color-pairs.

3. **Kempe-lock rule.** If a Kempe swap in \(G-v\) can turn one of those pairs into a singleton, then an incident edge of \(v\) becomes critical. Thus every allowed degree-6 vertex must be locally Kempe-rigid.

4. **Boundary rule.** A low-degree island of degree-6 vertices must have enough external constraints to prevent singleton creation by recoloring. Otherwise it is reducible.

5. **Clique-cut rule.** Separating cliques of size at most 3 are reducible: color the two sides and align colors on the clique.

For (c), the genuinely no-critical-edge reducible configurations are therefore:

- any vertex of degree \(3,4,\) or \(5\);
- any edge \(uv\) where some coloring of \(G-v\) makes \(u\)’s color unique on \(N(v)\);
- any degree-6 vertex whose neighbor-color pairing is not forced under all colorings of \(G-v\);
- small degree-6 clusters with too small a boundary to enforce all three color-pairs;
- clique cutsets of size \(\le 3\).

This subsumes adjacent 3-vertices, 3-paths of 3-vertices, and bridged \(G_3\)-components: those cannot even occur.

For (d): discharging alone is unlikely to close the \(k=4\) Dirac case. The Appel-Haken and Robertson-Sanders-Seymour-Thomas four-color proofs use discharging to force an unavoidable reducible configuration under a global curvature deficit; Cranston-Rabern style discharging similarly works when low structures must exist. Here the sign is wrong: no-critical-edge forces high minimum degree, so \(d(v)-4\) has surplus everywhere. Discharging may still narrow the search by proving that any example must be minimum degree at least 6, locally Kempe-rigid, and free of small separators, but closing the problem likely needs construction or a finite reducibility/Kempe-chain analysis beyond pure charge counting.

Sources: Robertson-Sanders-Seymour-Thomas, *JCTB* 70 (1997); Cranston-Rabern, “Edge Lower Bounds for List Critical Graphs, via Discharging”; Kostochka-Stiebitz, *JCTB* 87 (2003); Skottova-Steiner arXiv:2508.08703.
tokens used
52,629
The transplant as stated breaks at a basic point: in a 4-vertex-critical graph with no critical edge, there are no degree-3 vertices at all. In fact there are no degree-4 or degree-5 vertices either.

Let \(G\) be 4-vertex-critical and suppose \(uv\in E(G)\). Since \(G-v\) is 3-colorable, take a 3-coloring \(\phi\) of \(G-v\). If \(\phi(u)\) is the unique occurrence of its color on \(N(v)\), then \(\phi\) extends to a 3-coloring of \(G-uv\) by giving \(v\) the color \(\phi(u)\). Hence \(uv\) is critical. Therefore, in a graph with no critical edge, for every \(v\), every 3-coloring of \(G-v\) must color \(N(v)\) so that each of the three colors appears at least twice. Thus

\[
d(v)\ge 6 \quad \text{for every }v.
\]

So the degree-3 discharging picture is vacuous. Gallai’s low-vertex structure is useful for ordinary critical graphs, but here the no-critical-edge hypothesis kills the whole low-degree layer before discharging begins.

For (a): with \(c(v)=d(v)-4\),

\[
\sum_v c(v)=2|E|-4|V|.
\]

The Kostochka-Stiebitz bound gives \( |E|\ge (2+1/7)|V|\) for a spanning 4-critical subgraph, hence \(\sum c(v)\ge 2|V|/7\). But the no-critical-edge condition gives the stronger \(\delta(G)\ge 6\), so actually \(|E|\ge 3|V|\) and \(\sum c(v)\ge 2|V|\). There is no negative charge to absorb.

For (b), the correct propagation rule is not “send charge to 3-vertices”; it is:

1. **Singleton-color rule.** If some 3-coloring of \(G-v\) gives a neighbor \(u\) a color unique on \(N(v)\), then \(uv\) is critical. Forbidden.

2. **Neighbor-pairing rule.** If \(d(v)=6\), then in every 3-coloring of \(G-v\), the six neighbors of \(v\) must split exactly into three color-pairs.

3. **Kempe-lock rule.** If a Kempe swap in \(G-v\) can turn one of those pairs into a singleton, then an incident edge of \(v\) becomes critical. Thus every allowed degree-6 vertex must be locally Kempe-rigid.

4. **Boundary rule.** A low-degree island of degree-6 vertices must have enough external constraints to prevent singleton creation by recoloring. Otherwise it is reducible.

5. **Clique-cut rule.** Separating cliques of size at most 3 are reducible: color the two sides and align colors on the clique.

For (c), the genuinely no-critical-edge reducible configurations are therefore:

- any vertex of degree \(3,4,\) or \(5\);
- any edge \(uv\) where some coloring of \(G-v\) makes \(u\)’s color unique on \(N(v)\);
- any degree-6 vertex whose neighbor-color pairing is not forced under all colorings of \(G-v\);
- small degree-6 clusters with too small a boundary to enforce all three color-pairs;
- clique cutsets of size \(\le 3\).

This subsumes adjacent 3-vertices, 3-paths of 3-vertices, and bridged \(G_3\)-components: those cannot even occur.

For (d): discharging alone is unlikely to close the \(k=4\) Dirac case. The Appel-Haken and Robertson-Sanders-Seymour-Thomas four-color proofs use discharging to force an unavoidable reducible configuration under a global curvature deficit; Cranston-Rabern style discharging similarly works when low structures must exist. Here the sign is wrong: no-critical-edge forces high minimum degree, so \(d(v)-4\) has surplus everywhere. Discharging may still narrow the search by proving that any example must be minimum degree at least 6, locally Kempe-rigid, and free of small separators, but closing the problem likely needs construction or a finite reducibility/Kempe-chain analysis beyond pure charge counting.

Sources: Robertson-Sanders-Seymour-Thomas, *JCTB* 70 (1997); Cranston-Rabern, “Edge Lower Bounds for List Critical Graphs, via Discharging”; Kostochka-Stiebitz, *JCTB* 87 (2003); Skottova-Steiner arXiv:2508.08703.
