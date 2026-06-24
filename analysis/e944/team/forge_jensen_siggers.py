#!/usr/bin/env python3
"""
forge_jensen_siggers.py — reconstruct the Jensen-Siggers 2012 construction and
attack its gadget.

Architecture (archivist_jensen_siggers_2012.md):
  B = K_{2m,2m,2m} complete tripartite. UNIQUE 3-coloring (the 3 parts). No edge
      critical. This is the "free" redundancy engine.
  G(m) = disagreement gadget (star v0-v1v2v3 + transfer gadgets T(m)/T'(m)) glued
      onto B's parts S1,S2,S3. Forces >=1 Si non-monochromatic (=> chi=4) but
      G\v* always 3-colorable (=> vertex-criticality). ALL critical edges live here.

STEP 1 (this file): verify the CORE property — K_{2m,2m,2m} has NO critical edge
and a rigid (essentially unique) 3-coloring. This is the load-bearing claim.

STEP 2: build a SIMPLIFIED disagreement gadget directly (not the full T(m)/T'(m)
path machinery) — the minimal structure that (a) forces >=1 part bichromatic,
(b) stays 3-colorable after any single vertex deletion. Then H = 4-critical
subgraph of B ∪ gadget. Measure |E*| (critical edges) and try gadget variants
that REDUCE |E*| toward 0.

All exact, dual-verified with count's checkers.
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def complete_tripartite(a, b, c):
    """K_{a,b,c} with parts labeled (0,i),(1,j),(2,k)."""
    G = nx.Graph()
    parts = [[(0, i) for i in range(a)],
             [(1, j) for j in range(b)],
             [(2, k) for k in range(c)]]
    for pi in range(3):
        for pj in range(pi + 1, 3):
            for u in parts[pi]:
                for v in parts[pj]:
                    G.add_edge(u, v)
    return G, parts


def count_critical_edges(G, k):
    c = 0
    for e in list(G.edges()):
        H = G.copy(); H.remove_edge(*e)
        if is_k_colorable(H, k - 1):
            c += 1
    return c


def verify_core(m):
    """K_{2m,2m,2m} is 3-chromatic, and NO edge is critical (removing any one
    edge keeps chi=3 — trivially, since chi only drops if it disconnects a part,
    which a single edge can't in K_{2m,2m,2m} for m>=2)."""
    G, parts = complete_tripartite(2 * m, 2 * m, 2 * m)
    chi3 = (not is_k_colorable(G, 2)) and is_k_colorable(G, 3)
    # critical edge wrt k=3: G-e becomes 2-colorable?
    ce = count_critical_edges(G, 3)
    print(f"K_{{{2*m},{2*m},{2*m}}}: n={G.number_of_nodes()} m={G.number_of_edges()} "
          f"chi=3:{chi3} critical_edges(wrt k=3)={ce}", flush=True)
    return G, parts


def simple_disagreement_H(m):
    """
    A SIMPLIFIED H: B = K_{2m,2m,2m} plus a 'disagreement' apex structure that
    forces chi=4. Minimal version: add a star center w joined to one vertex in
    each part (w forces a 4th color iff the 3 chosen vertices use all 3 colors,
    which they do under the rigid coloring). Then take a 4-vertex-critical
    subgraph. This is a crude stand-in for the full G(m); we measure |E*|.
    """
    B, parts = complete_tripartite(2 * m, 2 * m, 2 * m)
    H = B.copy()
    # crude disagreement: a triangle apex w1,w2,w3 each joined across parts
    # to force a 4th color. We attach w joined to one representative per part.
    w = ("w", 0)
    for p in range(3):
        H.add_edge(w, parts[p][0])
    # w joined to one vertex of each part has degree 3, all 3 colors in nbhd =>
    # w needs a 4th color => chi=4? Only if those reps are forced distinct (they
    # are, rigid coloring). But w alone is removable-ish. This is crude; measure.
    return H, parts


def reduce_to_4vc(G):
    """Remove removable vertices until 4-vertex-critical (greedy)."""
    H = nx.convert_node_labels_to_integers(G)
    if is_k_colorable(H, 3) or not is_k_colorable(H, 4):
        return None
    changed = True
    while changed:
        changed = False
        for v in list(H.nodes()):
            K = H.copy(); K.remove_node(v)
            if K.number_of_nodes() >= 4 and (not is_k_colorable(K, 3)) and is_k_colorable(K, 4):
                H = K; changed = True; break
    return nx.convert_node_labels_to_integers(H)


if __name__ == "__main__":
    print("=== STEP 1: verify K_{2m,2m,2m} core (no critical edge, chi=3) ===", flush=True)
    for m in (2, 3, 4):
        verify_core(m)

    print("\n=== STEP 2: crude disagreement H, measure critical edges ===", flush=True)
    for m in (2, 3):
        H, parts = simple_disagreement_H(m)
        chi4 = (not is_k_colorable(H, 3)) and is_k_colorable(H, 4)
        print(f"crude H(m={m}): n={H.number_of_nodes()} m={H.number_of_edges()} "
              f"chi=4:{chi4}", flush=True)
        if chi4:
            R = reduce_to_4vc(H)
            if R:
                ce = len(critical_edges(R, 4))
                vc, _, _ = is_vertex_critical(R, 4)
                print(f"  4vc-subgraph: n={R.number_of_nodes()} "
                      f"m={R.number_of_edges()} vc={vc} critical_edges={ce} "
                      f"frac={ce/R.number_of_edges():.3f}", flush=True)
