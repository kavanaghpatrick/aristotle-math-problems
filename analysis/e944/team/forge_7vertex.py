#!/usr/bin/env python3
"""
forge_7vertex.py — exhaustive study of 4-regular graphs on 7 vertices.

We found 4-regular 7-vertex 14-edge graphs that are 4-vertex-critical with
exactly half (7/14) edges redundant. A 4-regular graph on 7 vertices is the
complement of a 2-regular graph on 7 vertices (= complement of a disjoint union
of cycles covering 7 vertices). The 2-regular graphs on 7 vertices are:
  C7, C3+C4.
So there are exactly 2 (up to iso) 4-regular graphs on 7 vertices:
  complement(C7) and complement(C3 cup C4).

Let's compute their criticality profile exactly, and check: is EITHER of them,
or any 7-vertex graph, a witness? Also exhaustively check all 7-vertex graphs
that are 4-vertex-critical for the minimum number of critical edges.
"""
import itertools
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, summary, is_e944_witness)


def complement_of_cycles(cycles, n=7):
    """Build complement of a union of given cycles (lists of node sequences)."""
    G2 = nx.Graph()
    G2.add_nodes_from(range(n))
    for cyc in cycles:
        for i in range(len(cyc)):
            G2.add_edge(cyc[i], cyc[(i + 1) % len(cyc)])
    return nx.complement(G2)


def profile(G, name):
    chi = chromatic_number(G)
    vc, _, bad = is_vertex_critical(G)
    ce = critical_edges(G, chi) if chi == 4 else []
    m = G.number_of_edges()
    print(f"[{name}] n={G.number_of_nodes()} m={m} chi={chi} "
          f"vertex_critical={vc} critical_edges={len(ce)} redundant={m-len(ce)}")
    return chi, vc, ce


def exhaustive_7vertex_min_critical():
    """
    Over ALL graphs on 7 labeled vertices that are 4-vertex-critical, find the
    minimum number of critical edges. (7 vertices -> 21 possible edges ->
    2^21 = 2M labeled graphs; too many to brute force naively, but we prune:
    must be 4-chromatic, connected, min-degree>=3.) We instead use nauty if
    available; else sample structured candidates.
    """
    # Try nauty geng
    import shutil, subprocess, os
    geng = shutil.which("geng")
    if geng is None:
        # common locations
        for cand in ["/opt/homebrew/bin/geng", "/usr/local/bin/geng",
                     os.path.expanduser("~/nauty/geng")]:
            if os.path.exists(cand):
                geng = cand
                break
    if geng is None:
        print("  geng (nauty) not found; skipping exhaustive 7-vertex sweep.")
        return None
    print(f"  using geng at {geng}")
    # 7 vertices, min degree 3 (4-critical needs min-deg >= k-1 = 3)
    out = subprocess.run([geng, "-c", "-d3", "7"], capture_output=True, text=True)
    lines = out.stdout.strip().split("\n")
    best = None
    count = 0
    for g6 in lines:
        if not g6.strip():
            continue
        G = nx.from_graph6_bytes(g6.strip().encode())
        if chromatic_number(G) != 4:
            continue
        vc, _, _ = is_vertex_critical(G)
        if not vc:
            continue
        ce = critical_edges(G, 4)
        count += 1
        if best is None or len(ce) < best[0]:
            best = (len(ce), g6.strip(), G.copy())
            print(f"  4-vc 7-vertex graph: m={G.number_of_edges()} "
                  f"critical_edges={len(ce)}  g6={g6.strip()}")
    print(f"  total 4-vertex-critical 7-vertex graphs: {count}")
    return best


if __name__ == "__main__":
    print("=== The two 4-regular graphs on 7 vertices ===")
    G_c7 = complement_of_cycles([[0, 1, 2, 3, 4, 5, 6]])
    profile(G_c7, "complement(C7)")
    G_c3c4 = complement_of_cycles([[0, 1, 2], [3, 4, 5, 6]])
    profile(G_c3c4, "complement(C3+C4)")

    print("\n=== Exhaustive: min critical edges over 4-vertex-critical 7-vertex graphs ===")
    best = exhaustive_7vertex_min_critical()
    if best:
        print(f"\nMIN critical edges on 7 vertices = {best[0]} (g6={best[1]})")
        if best[0] == 0:
            print("*** 7-VERTEX WITNESS EXISTS ***")
            is_e944_witness(best[2])
