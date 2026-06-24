# E944 Dirac k=4 — Stage 2 Cross-Domain Analogies (POST-CODEX PIVOT)

## Codex critique of original brief
The "minor-critical 4-subset" 4-uniform hypergraph H(G) is NOT canonical: K4-minor witnesses are noncanonical branch-set data and do not encode vertex-criticality or absence of critical edges. Frankl-Tokushige reconstruction does NOT deliver a finite N_0 because 4-critical cores have unbounded order.

## Corrected canonical object: edge-core clutter
For a 4-vertex-critical graph G, the canonical attached set system is
  C(G) = { E(F) : F subseteq G is a spanning 4-critical subgraph }.
This is a CLUTTER (no element is contained in another) on E(G). The
no-critical-edge condition is equivalent to
  intersection over F in C(G) of E(F) is empty.
Equivalently: every edge of G is omitted by at least one spanning 4-critical
subgraph. This encoding is exact, but not by itself a reconstruction bound.

## Critical-colouring hypergraph (Stiebitz-style)
For each vertex v in V(G), every proper 3-colouring c_v of G \ {v} exists since
G is 4-vertex-critical. The critical-colouring hypergraph H_chr(G) has vertex
set V(G) and a hyperedge for each colour class S of every 3-colouring of every
G \ {v}. This is the right Stiebitz-style structural object: hyperedges are
colour classes appearing in 3-colourings of subgraphs of G.

## Counting-identity engine
The relevant counting identities live in:
- Gallai's low-degree theorem: in a k-critical graph G with k >= 4, the
  subgraph of vertices of degree k-1 is a disjoint union of complete graphs
  K_{r_i} and odd cycles whose blocks have specific structure.
- Dirac's edge bound: in a k-critical graph, every edge has at least k-2
  common neighbours of its endpoints in some critical structure; this
  forces a lower-density linear-in-n edge count.
- Kostochka-Stiebitz colour-critical hypergraph edge bound (1994-2002):
  an r-critical r-uniform hypergraph H on n vertices has at least
  (r-1+1/(r-1)!) * n / 2 hyperedges; the bound TRANSFERS to the
  critical-colouring hypergraph H_chr(G) of a 4-vertex-critical G.

## Real seminal paper (verified May 30 2026 via arXiv)
Skottova, Ema and Steiner, Raphael (2025), "Critical edge sets in
vertex-critical graphs", arXiv:2508.08703 [math.CO], 24 pages.
- For all k > 4 they prove f_k(n) = Omega(n^{1/3}); k = 4 OPEN.
- They prove f_k(n) = O(n / (log n)^{Omega(1)}) for all k >= 4 (first
  nontrivial upper bound).
- Lower bounds via modified Jensen construction + gluing operation.
- Upper bounds via Conlon-Fox variant of the Szemeredi regularity lemma.

## Bridge to Aristotle
The honest reformulation: instead of seeking N_0 via reconstruction, seek
SUB-CLAIM CLOSURE at k = 4 by adapting Skottova-Steiner's gluing operation
(which already produces Omega(n^{1/3}) at k > 4) to the k = 4 boundary. The
obstruction at k = 4 is that Jensen's k >= 5 base case cannot be used; the
question is whether the gluing operation has a k = 4 base case at all.

## Sources
- Skottova-Steiner 2025: arXiv:2508.08703 (verified).
- Stiebitz, M. (1985), "Subgraphs of colour-critical graphs", Combinatorica 7.
- Kostochka, A. and Stiebitz, M. (1994), "Excess in colour-critical graphs",
  DIMACS Series 20.
- Gallai, T. (1963), "Critical graphs", in Proc. Smolenice 1963.
- Dirac, G. A. (1953), "Some theorems on abstract graphs", PLMS 2.
