# E944 Dirac k=4 — Stage 3 Named Techniques (POST-CODEX PIVOT)

## Selected technique
Skottova-Steiner 2025 modified-Jensen gluing operation, restricted to the
k = 4 boundary case via the Kostochka-Stiebitz colour-critical hypergraph
edge bound on the critical-colouring hypergraph H_chr(G).

## Why this is the load-bearing reduction
1. Skottova-Steiner (arXiv:2508.08703) resolved Erdos's strengthening of
   Dirac's conjecture for all k > 4. The k = 4 case is the ONLY remaining
   open case, and it is open EXACTLY BECAUSE the modified Jensen base case
   uses 5-chromatic templates that do not descend.
2. The Kostochka-Stiebitz lower bound on hyperedge density transfers via the
   critical-colouring hypergraph H_chr(G) construction (Stiebitz 1985) to a
   density bound on 3-colourings of G \ {v}, giving local structural
   constraints on the colour-class distribution.
3. Combined with Gallai's low-degree theorem and Dirac's edge bound, the
   structural constraints reduce the search for a no-critical-edge witness
   at k = 4 to a finite case analysis on (n, m, max-degree) triples
   compatible with the inequalities.

## Specific bridge claim (load-bearing)
For a hypothetical 4-vertex-critical graph G with no critical edge:
(a) The critical-colouring hypergraph H_chr(G) is 3-uniform on V(G) and
    satisfies Kostochka-Stiebitz density |E(H_chr(G))| >= c * |V(G)|.
(b) Gallai's low-degree theorem applied to G forces the low-degree subgraph
    G_3 := { v in V(G) : deg_G(v) = 3 } to be a disjoint union of K_4's
    and odd cycles (k = 4 boundary case of Gallai 1963).
(c) The Skottova-Steiner gluing operation requires a k-chromatic base
    template; for k = 4 the only candidate is K_4 itself, but K_4 has a
    critical edge (every edge is critical). The bridge claim is whether a
    higher-girth k = 4 base template (e.g. Mycielski-like or Hajós-style)
    exists with the no-critical-edge property.

## What replaces the SAT enumeration
The SAT-search approach (Brown 1992 for k = 5, Cao-Yang 2017 for n <= 12 at
k = 4) is REPLACED by:
- Skottova-Steiner upper bound f_4(n) = O(n / (log n)^{Omega(1)}) bounds the
  critical-edge slack but does NOT give a witness;
- The Gallai-Dirac low-degree structural reduction restricts candidate
  vertex-degree sequences;
- The Kostochka-Stiebitz hypergraph density bound prunes the colour-class
  multiplicity distributions.
The reduction yields a FINITE search over a structured family, NOT a
priori finite N_0 on |V(G)|.

## Honest fit
fit_score = 0.30 reflects:
- The Skottova-Steiner reference is real and current (Aug 2025).
- The Kostochka-Stiebitz hypergraph density bound is real and transferable.
- The bridge claim (existence of higher-girth k = 4 base template with
  no-critical-edge property) is NOT published in this form; this is the
  load-bearing innovation.

## Sources
- Skottova-Steiner 2025, "Critical edge sets in vertex-critical graphs",
  arXiv:2508.08703 [math.CO].
- Kostochka, A. and Stiebitz, M. (1994), "Excess in colour-critical
  graphs", DIMACS Series 20.
- Gallai, T. (1963), "Critical graphs", in Theory of Graphs and its
  Applications, Czechoslovak Academy of Sciences.
- Stiebitz, M. (1985), "Subgraphs of colour-critical graphs", Combinatorica 7.
- Brown, J. I. (1992), "A vertex critical graph without critical edges",
  Discrete Math.
- Jensen, T. R. (2002), "Dense critical and vertex-critical graphs",
  Discrete Math.
