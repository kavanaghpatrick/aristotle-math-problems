#!/usr/bin/env python3
"""
enumerate.py — exhaustive enumeration of 4-vertex-critical graphs on n vertices
and the critical-EDGE histogram. (count, E944 squad)

No nauty available, so we enumerate over all labeled graphs on n vertices using
networkx.graph_atlas (n<=7) or a direct bitmask enumeration with a cheap
isomorphism dedup. For n in 4..7 we use the exhaustive approach; results are the
COMPLETE set of 4-vertex-critical graphs (up to iso) on those n.

Output: histogram of num_critical_edges over all 4-vertex-critical graphs,
broken down by n. Any graph with 0 critical edges is an E944 witness and is
printed in full.
"""
import sys
import itertools
import networkx as nx
from critedge import (chromatic_number, is_vertex_critical, num_critical_edges,
                      critical_edges)


def canonical_form(G):
    """Cheap canonical key for dedup: use networkx weisfeiler-lehman hash plus
    invariants. WL hash is not a perfect canonical form but combined with
    (n,m,degseq,triangles) collisions across non-iso graphs are then resolved
    by an explicit is_isomorphic check in the caller's bucket."""
    n = G.number_of_nodes()
    m = G.number_of_edges()
    degseq = tuple(sorted(d for _, d in G.degree()))
    tri = sum(nx.triangles(G).values()) // 3
    wl = nx.weisfeiler_lehman_graph_hash(G, iterations=3)
    return (n, m, degseq, tri, wl)


def all_graphs_on_n(n):
    """Yield one representative of each isomorphism class of graphs on n labeled
    vertices, via graph_atlas_g for n<=7."""
    if n <= 7:
        from networkx.generators.atlas import graph_atlas_g
        atlas = graph_atlas_g()
        for G in atlas:
            if G.number_of_nodes() == n:
                yield G
    else:
        raise NotImplementedError("n>7 needs nauty; use targeted search instead")


def four_vertex_critical_on_n(n):
    """Return list of all 4-vertex-critical graphs on n vertices (iso classes)."""
    out = []
    for G in all_graphs_on_n(n):
        if G.number_of_nodes() != n:
            continue
        # must be connected with chi==4; quick filters first
        if G.number_of_edges() < (4 * 3) // 2:  # K4 has 6 edges; need >= some edges
            continue
        if chromatic_number(G) != 4:
            continue
        if is_vertex_critical(G, 4):
            out.append(G)
    return out


def main():
    print("=" * 70)
    print("Exhaustive 4-VERTEX-CRITICAL graph census + critical-edge histogram")
    print("(complete up to isomorphism for n in 4..7 via networkx atlas)")
    print("=" * 70)
    grand_hist = {}
    witnesses = []
    for n in range(4, 8):
        graphs = four_vertex_critical_on_n(n)
        hist = {}
        edgecounts = {}
        for G in graphs:
            ce = num_critical_edges(G)
            hist[ce] = hist.get(ce, 0) + 1
            grand_hist[ce] = grand_hist.get(ce, 0) + 1
            m = G.number_of_edges()
            edgecounts.setdefault(ce, []).append(m)
            if ce == 0:
                witnesses.append((n, G))
        total = len(graphs)
        print(f"\nn={n}: {total} four-vertex-critical graphs (iso classes)")
        if total:
            for ce in sorted(hist):
                mlist = edgecounts[ce]
                print(f"   #critical-edges={ce:>3}: {hist[ce]:>4} graphs "
                      f"(edge-counts {min(mlist)}..{max(mlist)})")
            mince = min(hist)
            print(f"   --> MIN critical-edge count over all n={n}: {mince}")
    print("\n" + "=" * 70)
    print("GRAND histogram of #critical-edges over all 4-vertex-critical graphs n=4..7:")
    for ce in sorted(grand_hist):
        print(f"   #critical-edges={ce:>3}: {grand_hist[ce]} graphs")
    print(f"   global MIN #critical-edges = {min(grand_hist)}")
    print("\nE944 WITNESSES (0 critical edges) found:", len(witnesses))
    for n, G in witnesses:
        print(f"   n={n} edges={sorted(G.edges())}")
    print("=" * 70)


if __name__ == "__main__":
    main()
