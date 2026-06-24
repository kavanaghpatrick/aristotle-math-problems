#!/usr/bin/env python3
"""
estar_structure.py — analyze the structure of E* (the critical-edge subgraph) of
a 4-vertex-critical graph. (count, E944)

Jensen-Siggers conjecture (archivist): if Dirac k=4 is FALSE, plausibly E* is
always CONNECTED and even SPANNING of positive size. Each annealing local minimum
is a data point: is E* connected? spanning? what's its component structure? If E*
is forced connected/spanning across all our best near-witnesses, that's
impossibility intel; if E* can be scattered into tiny pieces, that's existence intel.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from count_anneal import Graph


def analyze_estar(edges, n, label=""):
    g = Graph(n, edges)
    assert g.chi() == 4, f"{label}: chi != 4"
    # vertex-criticality
    vc = all(g.chi_minus_vertex(v) < 4 for v in range(n))
    ce = [(a, b) for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4]
    Estar = nx.Graph()
    Estar.add_nodes_from(range(n))
    Estar.add_edges_from(ce)
    # structure of E* (ignore isolated vertices for component analysis)
    Es = nx.Graph(); Es.add_edges_from(ce)
    touched = set(Es.nodes())
    ncomp = nx.number_connected_components(Es) if Es.number_of_edges() else 0
    spanned_vertices = len(touched)
    comp_sizes = sorted((len(c) for c in nx.connected_components(Es)), reverse=True) if Es.number_of_edges() else []
    is_spanning = (spanned_vertices == n)
    is_connected = (ncomp == 1)
    print(f"--- {label}: n={n} m={len(edges)} vertex-critical={vc}")
    print(f"    |E*| (critical edges) = {len(ce)}")
    print(f"    E* spans {spanned_vertices}/{n} vertices; spanning={is_spanning}")
    print(f"    E* components: {ncomp}, sizes (by #vertices): {comp_sizes}")
    print(f"    E* connected={is_connected}")
    # which vertices are NOT touched by any critical edge?
    untouched = [v for v in range(n) if v not in touched]
    print(f"    vertices with NO incident critical edge: {len(untouched)} {untouched if len(untouched)<=10 else '(>10)'}")
    return {"label": label, "n": n, "ncrit": len(ce), "spanning": is_spanning,
            "connected": is_connected, "ncomp": ncomp, "comp_sizes": comp_sizes,
            "untouched": len(untouched), "vertex_critical": vc}


def circulant_edges(n, S):
    E = []
    for d in S:
        for i in range(n): E.append((i, (i+d) % n))
    return E


if __name__ == "__main__":
    print("E* structure baseline on circulant champions + named graphs:\n")
    results = []
    results.append(analyze_estar(circulant_edges(7, [1,2]), 7, "C7(1,2)"))
    results.append(analyze_estar(circulant_edges(13, [1,2,5]), 13, "C13(1,2,5)"))
    results.append(analyze_estar(circulant_edges(16, [1,2,5]), 16, "C16(1,2,5)"))
    # K4
    results.append(analyze_estar([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], 4, "K4"))
    print("\nSUMMARY (Jensen-Siggers E*-connected/spanning check):")
    for r in results:
        print(f"  {r['label']:14s}: |E*|={r['ncrit']:3d} spanning={r['spanning']} "
              f"connected={r['connected']} comps={r['ncomp']} untouched_v={r['untouched']}")
    print("\nIf E* is ALWAYS connected+spanning across near-witnesses, supports")
    print("Jensen-Siggers 'E* connected/spanning of positive size' ⟹ no witness.")
