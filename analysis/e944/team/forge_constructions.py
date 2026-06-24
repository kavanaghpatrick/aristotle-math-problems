#!/usr/bin/env python3
"""
forge_constructions.py — E944 constructive toolbox.

Builds candidate 4-vertex-critical graphs with NO critical edge, using:
  - Hajos construction (Hajos sum / merge)
  - Mycielskian / generalized Mycielskian
  - Ore / Dirac (DHGO) compositions of smaller critical graphs
  - Gallai-tree boundary surgery
  - vertex/edge gluings, identifications

Each builder returns a networkx Graph. Verify with forge_verify.is_e944_witness.

DESIGN PRINCIPLE for the target (k=4,r=1):
  Every vertex critical (deleting any vertex 3-colorable)
  BUT every edge redundant (deleting any edge still chi=4).
  => 4-chromaticity must be witnessed by MULTIPLE obstructions through every
     edge, while vertex-deletion kills all obstructions at once.
"""
import itertools
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_e944_witness, is_k_colorable, summary)


def relabel_disjoint(G, prefix):
    """Relabel nodes with a prefix to make disjoint union safe."""
    return nx.relabel_nodes(G, {v: (prefix, v) for v in G.nodes()})


def hajos_sum(G1, e1, G2, e2):
    """
    Hajos construction of two graphs over chosen edges.
    e1=(x1,y1) in G1, e2=(x2,y2) in G2.
    Steps:
      1. Delete edge x1-y1 from G1, delete edge x2-y2 from G2.
      2. Identify y1 with x2 (call it the merge vertex).
      3. Add edge x1-y2.
    If G1, G2 are both k-critical, the Hajos sum is k-critical (vertex-critical
    is NOT automatic; classically Hajos preserves k-chromaticity, and for
    k-critical inputs it produces a k-critical graph).
    """
    x1, y1 = e1
    x2, y2 = e2
    H1 = relabel_disjoint(G1, "A")
    H2 = relabel_disjoint(G2, "B")
    x1, y1 = ("A", x1), ("A", y1)
    x2, y2 = ("B", x2), ("B", y2)
    H = nx.union(H1, H2)
    H.remove_edge(x1, y1)
    H.remove_edge(x2, y2)
    # identify y1 and x2
    H = nx.contracted_nodes(H, y1, x2, self_loops=False)
    # add edge x1 - y2
    H.add_edge(x1, y2)
    return nx.convert_node_labels_to_integers(H)


def ore_composition(G1, e1, G2, v2):
    """
    Ore composition (DHGO): split a vertex v2 of G2 across edge e1=(x1,y1) of G1.
    Replace edge x1-y1 of G1 by a copy of G2-v2, distributing the neighbors of v2
    between x1 and y1. This is the classical way to build k-critical graphs of
    higher order. Many variants; we implement the simplest balanced split.
    """
    x1, y1 = e1
    H1 = relabel_disjoint(G1, "A")
    x1, y1 = ("A", x1), ("A", y1)
    H2 = relabel_disjoint(G2, "B")
    v2 = ("B", v2)
    H = nx.union(H1, H2)
    H.remove_edge(x1, y1)
    nbrs = list(H2.neighbors(v2))
    H.remove_node(v2)
    # split neighbors of v2 between x1 and y1
    half = len(nbrs) // 2
    for w in nbrs[:half]:
        H.add_edge(x1, w)
    for w in nbrs[half:]:
        H.add_edge(y1, w)
    return nx.convert_node_labels_to_integers(H)


def generalized_mycielskian(G, m):
    """
    Generalized Mycielskian M_m(G): m levels of vertex copies plus an apex.
    m=1 is the ordinary Mycielskian. Increases chromatic number by 1 when m>=1
    for graphs of chi>=2 (with conditions). Preserves vertex-criticality of G
    in many cases.
    Levels: L_0 = original V; L_1..L_{m} = copies; apex z connected to L_m.
    Edges:
      - L_0 keeps G's edges.
      - for i in 1..m: u_i ~ w_{i-1} whenever u~w in G (and to w_{i+1}? no).
        Standard cone construction: vertex u at level i adjacent to neighbors of
        u at level i-1.
      - apex z adjacent to all of L_m.
    """
    H = nx.Graph()
    V = list(G.nodes())
    # level 0
    for v in V:
        H.add_node((0, v))
    for u, w in G.edges():
        H.add_edge((0, u), (0, w))
    # levels 1..m
    for i in range(1, m + 1):
        for v in V:
            H.add_node((i, v))
        for u, w in G.edges():
            # u at level i adjacent to w at level i-1, and w at level i to u at level i-1
            H.add_edge((i, u), (i - 1, w))
            H.add_edge((i, w), (i - 1, u))
    # apex
    z = ("apex", 0)
    H.add_node(z)
    for v in V:
        H.add_edge(z, (m, v))
    return nx.convert_node_labels_to_integers(H)


def toft_graph():
    """
    A known 4-chromatic, 4-vertex-critical graph family (Toft). Placeholder:
    we build the 'Toft' / 'Hajos' style graph by Hajos-summing K4's.
    """
    K4 = nx.complete_graph(4)
    return hajos_sum(K4, (0, 1), K4, (0, 1))


def double_through_every_edge_probe(G):
    """
    Diagnostic: for each edge e, is there a 4-critical subgraph avoiding e?
    Equivalently chi(G-e)=4 iff some odd/obstruction survives. Reports the
    fraction of edges that are redundant.
    """
    chi = chromatic_number(G)
    if chi != 4:
        return None
    ce = critical_edges(G, chi)
    m = G.number_of_edges()
    return {"chi": chi, "m": m, "redundant_edges": m - len(ce),
            "critical_edges": len(ce),
            "frac_redundant": (m - len(ce)) / m if m else 0.0}


if __name__ == "__main__":
    print("=== Construction probes ===")
    # Hajos sum of two K4's
    H = hajos_sum(nx.complete_graph(4), (0, 1), nx.complete_graph(4), (0, 1))
    summary(H, "Hajos(K4,K4)")
    print("  ", double_through_every_edge_probe(H))

    # Generalized Mycielskian of K3 (= Grotzsch when m=1 of C5; here K3)
    for m in (1, 2, 3):
        M = generalized_mycielskian(nx.complete_graph(3), m)
        summary(M, f"genMyc(K3, m={m})")

    # Generalized Mycielskian of C5
    for m in (1, 2):
        M = generalized_mycielskian(nx.cycle_graph(5), m)
        summary(M, f"genMyc(C5, m={m})")
