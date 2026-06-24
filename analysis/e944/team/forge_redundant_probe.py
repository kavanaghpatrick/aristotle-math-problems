#!/usr/bin/env python3
"""
forge_redundant_probe.py — Find any 4-vertex-critical graph with >=1 redundant edge.

The target needs ALL edges redundant. A necessary precursor: does there exist a
4-vertex-critical graph with EVEN ONE non-critical edge? If we can find graphs
with k redundant edges and push k up toward m, we are on the right track.

We scan:
  - random 4-critical-ish graphs (build random graph, take a 4-critical subgraph
    by removing non-critical vertices) -- too noisy; instead we use targeted
    families known to be vertex-critical but NOT edge-critical.

KEY THEORY:
  A graph is "edge-critical" (= k-critical in the classical Dirac sense) iff
  every edge is critical AND it's k-chromatic. The classical k-critical graphs
  are ALL edge-critical. The Erdos-944 object is VERTEX-critical but maximally
  FAR from edge-critical. These are genuinely different.

  Brown's k=5 construction and Jensen's k>=5 give vertex-critical, edge-redundant.
  We need k=4.

Strategy here: start from a graph that is 4-chromatic and vertex-critical but
built to have parallel obstructions. We test the 'doubled' / 'thickened'
constructions: replace structures so every edge lies on >=2 independent
4-chromatic obstructions.
"""
import itertools
import random
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, summary)


def make_vertex_critical_4(G):
    """
    Given a 4-chromatic G, repeatedly remove non-critical vertices until
    vertex-critical (a 4-vertex-critical subgraph). Returns None if chi != 4.
    """
    H = G.copy()
    if chromatic_number(H) != 4:
        return None
    changed = True
    while changed:
        changed = False
        for v in list(H.nodes()):
            K = H.copy()
            K.remove_node(v)
            if chromatic_number(K) == 4:
                # v is NOT critical -> remove it, stay 4-chromatic
                H = K
                changed = True
                break
    return H


def count_redundant(G):
    """Return (#redundant edges, #critical edges, m) for a 4-chromatic G."""
    chi = chromatic_number(G)
    if chi != 4:
        return None
    ce = critical_edges(G, chi)
    m = G.number_of_edges()
    return (m - len(ce), len(ce), m)


def random_4critical_scan(n, p, trials, seed=0):
    """Scan random G(n,p), reduce to 4-vertex-critical, report redundant-edge counts."""
    random.seed(seed)
    best = None
    results = []
    for t in range(trials):
        G = nx.gnp_random_graph(n, p, seed=seed + t)
        if chromatic_number(G) != 4:
            continue
        H = make_vertex_critical_4(G)
        if H is None or H.number_of_nodes() == 0:
            continue
        vc, chi, bad = is_vertex_critical(H)
        if not vc or chi != 4:
            continue
        cr = count_redundant(H)
        if cr is None:
            continue
        red, crit, m = cr
        results.append((red, crit, m, H.number_of_nodes()))
        if best is None or red > best[0]:
            best = (red, crit, m, H.copy())
            print(f"  trial {t}: n={H.number_of_nodes()} m={m} "
                  f"redundant={red} critical={crit}"
                  + ("  <-- NEW BEST" if red > 0 else ""))
    return best, results


if __name__ == "__main__":
    print("=== Random 4-vertex-critical scan: looking for redundant edges ===")
    for (n, p) in [(8, 0.5), (10, 0.45), (12, 0.4), (14, 0.38), (16, 0.35),
                   (18, 0.33), (20, 0.32)]:
        print(f"\n-- G({n},{p}) --")
        best, results = random_4critical_scan(n, p, trials=200, seed=1)
        if results:
            maxred = max(r[0] for r in results)
            print(f"  scanned {len(results)} 4-vertex-critical graphs; "
                  f"max redundant edges = {maxred}")
        else:
            print("  no 4-vertex-critical graphs found")
