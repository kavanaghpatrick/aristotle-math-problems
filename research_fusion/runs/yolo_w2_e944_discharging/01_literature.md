# Literature scan — Erdős 944 Dirac k=4 via discharging method

## Status of Dirac k=4 (May 2026)
- Original conjecture: Dirac 1970 — for every k ≥ 4, ∃ a finite simple graph G with χ(G)=k, every vertex critical, no critical edge.
- k=5: Brown 1992, Discrete Math.
- All k with (k-1) non-prime: Lattanzio 2002, Discrete Math.
- k ≥ 5 uniformly: Jensen 2002, Discrete Math.
- Quantitative f_k(n) bounds for k ≥ 4 and k > 4 (no-critical-edge-set of size ≤ r): Martinsson-Steiner 2025, Combin. Probab. Comput.; Skottova-Steiner 2025 arXiv:2508.08703 (lower Ω(n^{1/3}) for k>4, upper O(n/(log n)^Ω(1)) for k≥4).
- k=4 r=1 remains OPEN. Skottova-Steiner explicitly leaves k=4 open with "fundamental obstacles for circulant constructions in that case."

## Discharging method — has anyone applied it to k=4 Dirac?
Grok web search (May 30 2026): **NO direct evidence**. The discharging method has been applied to k-list-critical graphs (Cranston-Rabern 2017 arXiv:1602.02589 "Edge Lower Bounds for List-Critical Graphs Via Discharging"; Cranston-Rabern 2017 survey arXiv:1306.4434 "An introduction to the discharging method via graph coloring") but never targeted the no-critical-edge property of Dirac.

## Key citations
- Robertson-Sanders-Seymour-Thomas 1997, "The four-colour theorem", J. Combin. Theory Ser. B 70 — 32 discharging rules, 633 reducible configurations.
- Cranston-Rabern 2017, "Edge Lower Bounds for List-Critical Graphs via Discharging" arXiv:1602.02589.
- Cranston-Rabern 2017 survey, arXiv:1306.4434.
- Kostochka-Stiebitz 1999, "A new lower bound on the number of edges in colour-critical graphs", J. Combin. Theory B 87: |E(G)| ≥ ((k/2) + (k-3)/(k²-2k-1))·|V(G)| - O(1) for k-critical G.
- Gallai 1963: vertices of degree k-1 in a k-critical graph induce a "Gallai forest" — disjoint union of K_r (r ≤ k-1) blocks and odd cycles.
- Stiebitz 1985: critical-colouring hypergraph H_chr(G).
- Martinsson-Steiner 2025, Skottova-Steiner 2025 arXiv:2508.08703.
- Brown 1992 (k=5 affirmative), Jensen 2002 (k≥5).

## Key structural fact (codex consultation May 30 2026)
**δ(G) ≥ 6** is forced by no-critical-edge + 4-vertex-criticality.

Proof sketch (R1 + C3): Let G be a hypothetical witness. For any vertex v, take a 3-coloring c of G - v (exists since G is 4-vertex-critical). In c restricted to N(v), all 3 colors must appear (else v could extend to a 3-coloring of G, contradicting χ(G)=4). If d(v) ≤ 5, by pigeonhole some color appears exactly once on N(v), say on u. Then re-color v with that color: this gives a 3-coloring of G - uv. So χ(G - uv) ≤ 3 < 4, i.e., uv IS critical, contradicting no-critical-edge. Hence d(v) ≥ 6 for all v.

Combined with Kostochka-Stiebitz lower-bound machinery, this is a genuine structural restriction on the open case — δ(G) ≥ 6 forces |E(G)| ≥ 3|V(G)|, so the initial Euler charge sum becomes 2|E| - 4|V| ≥ 2|V|, every vertex has charge ≥ 2. The straight discharging via c(v) = d(v) - 4 has no negative vertices to discharge to, so it does not directly close k=4 — but the lemma δ(G) ≥ 6 is itself a substantial new restriction (no published work states this for Dirac k=4 specifically).
