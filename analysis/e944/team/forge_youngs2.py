#!/usr/bin/env python3
"""
forge_youngs2.py — CORRECT non-bipartite quadrangulations of RP^2, then test
edge-criticality of the parity obstruction.

Construction (standard): take a disk quadrangulated by R concentric rings of
2k vertices each (ring r = vertices (r,0..2k-1)), with:
  - ring edges: (r,i)-(r,i+1)
  - radial edges between consecutive rings forming quad faces: (r,i)-(r+1,i)
This is a bipartite cylinder. To make RP^2: glue the OUTER boundary ring to
itself ANTIPODALLY: (R,i) ~ (R, i+k). For the faces to stay quads and the
result NON-BIPARTITE, the antipodal gluing must shift the bipartition. We test
chi to confirm non-bipartite + Youngs (chi=4).

Also the CANONICAL smallest examples directly:
  - K4 (the minimal projective quadrangulation): all edges critical (baseline).
  - "pseudo double wheel" PDW_n: a 2n-cycle v_0..v_{2n-1} plus two hubs a,b where
    a ~ even vertices, b ~ odd vertices, and a ~ b. Faces are quads
    (a,v_{2i},v_{2i+1},b)... we test which embed/quadrangulate and are chi=4.

The point: among the chi=4 non-bipartite quadrangulations, find those that are
4-vertex-critical and measure critical-edge count. The mechanism is the global
ℤ2 parity; the question is whether it survives single-edge deletion.
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def chi_of(G):
    if is_k_colorable(G, 2): return 2
    if is_k_colorable(G, 3): return 3
    if is_k_colorable(G, 4): return 4
    return 5


def disk_antipodal_rp2(k, R, shift=None):
    """
    R rings of 2k vertices; outer ring glued antipodally with given shift.
    Inner ring r=0 is a single cycle; we also add a center to cap the innermost
    face as quads-ish. We test chi regardless.
    """
    if shift is None:
        shift = k
    G = nx.Graph()
    def V(r, i): return (r, i % (2 * k))
    for r in range(R):
        for i in range(2 * k):
            G.add_edge(V(r, i), V(r, i + 1))
            if r + 1 < R:
                G.add_edge(V(r, i), V(r + 1, i))
    # antipodal glue of outer ring r=R-1
    for i in range(k):
        G = nx.contracted_nodes(G, V(R - 1, i), V(R - 1, i + shift), self_loops=False)
    # cap the center: connect innermost ring alternately to a center hub? Leave open.
    return nx.convert_node_labels_to_integers(G)


def pseudo_double_wheel(n):
    """2n-cycle + two hubs a (adj even), b (adj odd), a-b. Non-bipartite RP^2 quad."""
    G = nx.Graph()
    N = 2 * n
    for i in range(N):
        G.add_edge(("c", i), ("c", (i + 1) % N))
    for i in range(N):
        if i % 2 == 0:
            G.add_edge("a", ("c", i))
        else:
            G.add_edge("b", ("c", i))
    G.add_edge("a", "b")
    return nx.convert_node_labels_to_integers(G)


def mobius_quadrangulation(k):
    """
    Mobius-Kantor style: 2k-cycle with antipodal 'rungs' creating a Mobius band
    quadrangulation, boundary-glued. Vertices Z_{2k}; rungs i -- i+k make a
    Mobius ladder (which is a quadrangulation of the Mobius band / RP^2 minus a
    disk). For ODD k the Mobius ladder is non-bipartite.
    """
    G = nx.Graph()
    n = 2 * k
    for i in range(n):
        G.add_edge(i, (i + 1) % n)
    for i in range(k):
        G.add_edge(i, i + k)
    return G


def report(G, name):
    G = nx.convert_node_labels_to_integers(G)
    chi = chi_of(G)
    if chi != 4:
        print(f"[{name}] n={G.number_of_nodes()} m={G.number_of_edges()} chi={chi}", flush=True)
        return None
    vc, _, bad = is_vertex_critical(G, 4)
    ce = critical_edges(G, 4)
    m = G.number_of_edges()
    print(f"[{name}] n={G.number_of_nodes()} m={m} chi=4 vc={vc} "
          f"noncrit_v={len(bad)} |E*|={len(ce)} redundant={m-len(ce)} "
          f"({100*(m-len(ce))//m if m else 0}%)", flush=True)
    if vc and len(ce) == 0:
        edges = [tuple(sorted(e)) for e in G.edges()]
        if checkers.is_erdos944_k_r1(edges, G.number_of_nodes(), 4):
            print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
            return ("W", G)
    return (len(ce) if vc else None, G)


if __name__ == "__main__":
    print("=== K4 baseline (minimal RP^2 quadrangulation) ===", flush=True)
    report(nx.complete_graph(4), "K4")

    print("\n=== Pseudo-double-wheel PDW_n ===", flush=True)
    for n in range(2, 12):
        report(pseudo_double_wheel(n), f"PDW_{n}")

    print("\n=== Mobius ladder quadrangulation (odd k => non-bipartite) ===", flush=True)
    for k in range(3, 14):
        report(mobius_quadrangulation(k), f"Mobius_k={k}")

    print("\n=== Disk antipodal RP^2 (various shifts) ===", flush=True)
    for k in (3, 4, 5):
        for R in (2, 3):
            for shift in (k, 1):
                report(disk_antipodal_rp2(k, R, shift), f"disk(k={k},R={R},sh={shift})")
