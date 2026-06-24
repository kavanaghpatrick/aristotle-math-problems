#!/usr/bin/env python3
"""
forge_overlay.py — asymmetric multi-gadget overlay construction.

IDEA: a non-critical edge e means G-e still has a 4-critical subgraph avoiding e.
To make EVERY edge non-critical, cover the vertex set with TWO (or more)
edge-DISJOINT 4-chromatic subgraphs H1, H2 such that:
  - G = H1 ∪ H2 (same vertices, disjoint edge sets),
  - removing any edge of H1 leaves H2 ⊆ G-e still 4-chromatic  => e non-critical,
  - removing any edge of H2 leaves H1 still 4-chromatic        => e non-critical,
  - G is vertex-critical: deleting any vertex v makes BOTH H1-v and H2-v (and the
    whole G-v) 3-colorable simultaneously.

The tension: H1 and H2 must each be 4-chromatic on (most of) the vertex set, but
G-v must be 3-colorable, so EVERY vertex must be essential to BOTH H1 and H2's
4-chromaticity. That's why both H1 and H2 should themselves be vertex-critical
4-critical graphs on the SAME vertex set, edge-disjoint.

So: find two edge-disjoint 4-vertex-critical graphs on a common vertex set V.
Their union is then:
  - 4-chromatic (contains a 4-chromatic subgraph),
  - every edge non-critical (the OTHER subgraph survives),
  - vertex-critical IF deleting any v makes the union 3-colorable.

The last condition is the hard one and is NOT automatic (union may need fewer
deletions). We search for compatible pairs.
"""
import itertools
import random
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, is_e944_witness)


def two_edge_disjoint_4critical(base_nodes, g6_a, g6_b, perm=None):
    """
    Place two 4-vertex-critical graphs (given by graph6) on the SAME node set,
    optionally permuting the second, and union if edge-disjoint.
    Returns the union graph G or None if edges overlap.
    """
    Ha = nx.from_graph6_bytes(g6_a.encode())
    Hb = nx.from_graph6_bytes(g6_b.encode())
    if Ha.number_of_nodes() != Hb.number_of_nodes():
        return None
    n = Ha.number_of_nodes()
    if perm is not None:
        Hb = nx.relabel_nodes(Hb, {i: perm[i] for i in range(n)})
    Ea = set(tuple(sorted(e)) for e in Ha.edges())
    Eb = set(tuple(sorted(e)) for e in Hb.edges())
    if Ea & Eb:
        return None  # not edge-disjoint
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(Ea | Eb)
    return G


def search_overlay_pair(g6_list, n, trials_per_pair=400, seed=0):
    """
    For each pair of 4-vertex-critical graphs on n nodes, try random vertex
    permutations of the 2nd to get an edge-disjoint union that is a witness.
    """
    rng = random.Random(seed)
    best = None
    checked = 0
    for g6_a, g6_b in itertools.combinations_with_replacement(g6_list, 2):
        for t in range(trials_per_pair):
            perm = list(range(n))
            rng.shuffle(perm)
            G = two_edge_disjoint_4critical(range(n), g6_a, g6_b, perm)
            if G is None:
                continue
            if min(dict(G.degree()).values()) < 3:
                continue
            checked += 1
            # quick chi check
            if is_k_colorable(G, 3):
                continue
            if not is_k_colorable(G, 4):
                continue  # chi >= 5, not what we want
            # chi == 4. count critical edges.
            ce = critical_edges(G, 4)
            vc, _, bad = is_vertex_critical(G, 4)
            score = (0 if vc else 1, len(ce))  # prefer vertex-critical, then few crit edges
            if best is None or score < best[0]:
                best = (score, G.copy(), g6_a, g6_b, tuple(perm), vc, len(ce))
                print(f"  pair({g6_a},{g6_b}) perm: n={G.number_of_nodes()} "
                      f"m={G.number_of_edges()} chi=4 vertex_critical={vc} "
                      f"critical_edges={len(ce)}", flush=True)
                if vc and len(ce) == 0:
                    print("  *** WITNESS ***", flush=True)
                    return best
    print(f"  (checked {checked} edge-disjoint chi=4 unions)")
    return best


if __name__ == "__main__":
    # 4-vertex-critical graphs found earlier (the n=9 and n=10 catalogs).
    # Build a small catalog of 4-vertex-critical graphs on n=9 and n=10 nodes.
    import subprocess, shutil, os
    GENG = "/opt/homebrew/bin/geng"

    def catalog_4vc(n, limit=400):
        out = subprocess.run([GENG, "-c", "-d3", str(n)],
                             capture_output=True, text=True)
        res = []
        for g6 in out.stdout.split():
            G = nx.from_graph6_bytes(g6.encode())
            if is_k_colorable(G, 3) or not is_k_colorable(G, 4):
                continue
            ok = all(is_k_colorable(nx.restricted_view(G, [v], []), 3)
                     for v in [])  # placeholder
            # proper vertex-critical check
            vc = True
            for v in G.nodes():
                H = G.copy(); H.remove_node(v)
                if not is_k_colorable(H, 3):
                    vc = False; break
            if vc:
                res.append(g6)
            if len(res) >= limit:
                break
        return res

    for n in (9, 10):
        print(f"=== Overlay search on n={n} ===")
        cat = catalog_4vc(n)
        print(f"  catalog: {len(cat)} 4-vertex-critical graphs on {n} nodes")
        best = search_overlay_pair(cat[:30], n, trials_per_pair=300, seed=11)
        if best and best[5] and best[6] == 0:
            G = best[1]
            is_e944_witness(G)
            break
