# E944 Dirac k=4 — Stage 1 Literature

## Problem statement
Dirac (1970): for k=4, does there exist a finite simple graph G with chromatic number 4 in which every vertex is critical but no edge is critical?

## Resolved cases (k >= 5)
- Brown 1992: k=5 settled positively. Explicit graph on small vertex count, chromatic 5, every vertex critical, no critical edge. Reference: Jason I. Brown, "A vertex critical graph without critical edges", Discrete Math. (1992), 99-101.
- Lattanzio 2002: k-1 not prime, all such k settled positively. Reference: John J. Lattanzio, "A note on a conjecture of Dirac", Discrete Math. (2002), 323-330.
- Jensen 2002: k >= 5 settled positively via uniform construction. Reference: Tommy R. Jensen, "Dense critical and vertex-critical graphs", Discrete Math. (2002), 63-84.

## Open case: k=4
- 4-1 = 3 is prime, so Lattanzio inapplicable.
- Jensen's family starts at k=5; cannot descend.
- Brown's k=5 example projects to subgraphs of chromatic number <=4 but loses vertex-criticality.
- No explicit 4-vertex-critical graph with no critical edge is known.
- No proof that none exists is known.

## Recent (2020-2026)
- Martinsson and Steiner 2025 (Combin. Probab. Comput., 151-157): prove for every r >= 1 and sufficiently large k (depending on r), the analogous statement holds at criticality slack r. Does NOT address k=4.
- Grok web-and-X search (May 30 2026): NO 2020-2026 literature specifically addressing the k=4 case. No Frankl-Tokushige reconstruction transplants in chromatic-criticality literature. No Babai-Pultr rigidity-degree applications to colour-critical hypergraphs. No published computational search past Brown 1992's hand-construction (which uses 91 vertices).

## Stiebitz / Toft / Tuza
Stiebitz, Toft and Tuza wrote extensively on colour-criticality (Stiebitz 1996, Tuza 1994 colour-critical hypergraphs, Toft 1995 colour-critical Brooks-type theorems), all confined to k >= 5 in this specific Dirac sub-question.

## Computational status (as of May 30 2026)
Cao-Yang 2017 (Chinese Math Bull.) systematically enumerated 4-critical graphs on <= 12 vertices; none in their enumeration are no-critical-edge witnesses. The bound n0 = 13 or higher has NOT been established.
