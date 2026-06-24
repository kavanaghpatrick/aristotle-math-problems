#!/usr/bin/env python3
"""Dissect the n=7 4-vertex-critical graphs: locate NON-critical edges and study
their structure. (count, E944)"""
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from critedge import (chromatic_number, is_vertex_critical, num_critical_edges,
                      critical_edges)

atlas = graph_atlas_g()
graphs7 = [G for G in atlas if G.number_of_nodes() == 7
           and chromatic_number(G) == 4 and is_vertex_critical(G, 4)]

print(f"n=7 4-vertex-critical graphs: {len(graphs7)}\n")
for idx, G in enumerate(graphs7):
    m = G.number_of_edges()
    ce = critical_edges(G)
    crit = set(frozenset(e) for e in ce)
    noncrit = [e for e in G.edges() if frozenset(e) not in crit]
    degs = dict(G.degree())
    print(f"--- graph {idx}: m={m}, #critical={len(ce)}, #non-critical={len(noncrit)}")
    print(f"    degree sequence: {sorted(degs.values())}")
    print(f"    edges: {sorted(tuple(sorted(e)) for e in G.edges())}")
    print(f"    NON-critical edges: {sorted(tuple(sorted(e)) for e in noncrit)}")
    # For each non-critical edge, what is chi(G-e)? should stay 4
    for e in noncrit:
        H = G.copy(); H.remove_edge(*e)
        # is the edge in a triangle? endpoints' common neighbors
        cn = set(G.neighbors(e[0])) & set(G.neighbors(e[1]))
        print(f"      e={tuple(sorted(e))}: chi(G-e)={chromatic_number(H)} "
              f"endpoint-degs=({degs[e[0]]},{degs[e[1]]}) "
              f"#common-neighbors(triangles through e)={len(cn)}")
    # critical edges: triangle membership
    print(f"    critical-edge triangle profile:")
    for e in ce:
        cn = set(G.neighbors(e[0])) & set(G.neighbors(e[1]))
        print(f"      e={tuple(sorted(e))}: endpoint-degs=({degs[e[0]]},{degs[e[1]]}) "
              f"#triangles={len(cn)}")
    print()
