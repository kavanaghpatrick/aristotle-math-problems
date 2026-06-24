#!/usr/bin/env python3
"""
forge_assault_covers.py — voltage-graph / double covers of C13(1,2,5) and
related 6-regular near-misses, to break vertex-transitivity while doubling each
obstruction so the critical diff-1 orbit becomes redundant.

VOLTAGE GRAPH CONSTRUCTION (Gross-Tucker): take base graph B with Z_2 (or Z_m)
voltages on edges. The derived cover graph has vertex set V(B) x Z_m, and edge
((u,a),(v,a+volt(u,v))) for each base edge uv. Different voltage assignments give
different covers; a NONTRIVIAL voltage on the diff-1 orbit creates a twisted
double cover where each original obstruction lifts to TWO, plausibly making the
diff-1 edges redundant in the cover.

We enumerate Z_2 voltage assignments on the 3 edge-orbits of C13(1,2,5) (only 8
combos: voltage in {0,1} per orbit) plus a few Z_3 covers, build the cover, and
test χ / vertex-criticality / critical edges. Cover of a 6-regular graph is
6-regular on 2n (or mn) vertices — still satisfies SkSt δ≥6.

Also: canonical double cover (bipartite double / Kronecker cover with K2) — though
that's bipartite-ish and likely 2-colorable on top, so we focus on twisted covers
with voltages that keep odd structure.
"""
import itertools
import networkx as nx
from forge_verify import (is_k_colorable, is_vertex_critical, critical_edges)
import checkers


def circ(n, S):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for i in range(n):
        for s in S:
            G.add_edge(i, (i + s) % n)
    return G


def is_4vc_nx(G):
    if is_k_colorable(G, 3) or not is_k_colorable(G, 4):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def crit_count(G):
    return len(critical_edges(G, 4))


def edge_length(u, v, n):
    d = (u - v) % n
    return min(d, n - d)


def voltage_cover(n, S, m, volt_by_len):
    """
    Z_m voltage cover of C_n(S). volt_by_len: dict length->voltage in Z_m.
    Vertices: (i, a) for i in Z_n, a in Z_m.
    For each base edge (i, i+s): voltage = volt_by_len[length] in direction +s.
    Edge between (i,a) and ((i+s)%n, (a+volt)%m).
    """
    G = nx.Graph()
    for i in range(n):
        for a in range(m):
            G.add_node((i, a))
    for i in range(n):
        for s in S:
            j = (i + s) % n
            L = edge_length(i, j, n)
            volt = volt_by_len.get(L, 0)
            for a in range(m):
                G.add_edge((i, a), (j, (a + volt) % m))
    return nx.convert_node_labels_to_integers(G)


def dual_witness(G):
    if not is_4vc_nx(G) or crit_count(G) != 0:
        return False
    G2 = nx.convert_node_labels_to_integers(G)
    edges = [tuple(sorted(e)) for e in G2.edges()]
    return checkers.is_erdos944_k_r1(edges, G2.number_of_nodes(), k=4)


def profile(G, name):
    if is_k_colorable(G, 3):
        print(f"[{name}] chi<=3 (n={G.number_of_nodes()})", flush=True); return None
    if not is_k_colorable(G, 4):
        print(f"[{name}] chi>=5 (n={G.number_of_nodes()})", flush=True); return None
    vc, _, bad = is_vertex_critical(G, 4)
    ce = critical_edges(G, 4)
    m = G.number_of_edges()
    print(f"[{name}] n={G.number_of_nodes()} m={m} chi=4 vc={vc} "
          f"noncrit_v={len(bad)} critical_edges={len(ce)} "
          f"redundant={m-len(ce)}", flush=True)
    if vc and len(ce) == 0 and dual_witness(G):
        print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
        return ("WITNESS", G)
    return (len(ce) if vc else None, G)


if __name__ == "__main__":
    base_S = (1, 2, 5)
    n = 13
    best = None
    print("=== Z2 voltage covers of C13(1,2,5) ===", flush=True)
    for v1, v2, v5 in itertools.product((0, 1), repeat=3):
        if (v1, v2, v5) == (0, 0, 0):
            continue  # trivial cover = 2 disjoint copies
        vb = {1: v1, 2: v2, 5: v5}
        G = voltage_cover(n, base_S, 2, vb)
        r = profile(G, f"Z2cover v(1,2,5)=({v1},{v2},{v5})")
        if r and r[0] == "WITNESS":
            best = r; break
        if r and isinstance(r[0], int) and (best is None or
                (isinstance(best[0], int) and r[0] < best[0])):
            best = r

    if not (best and best[0] == "WITNESS"):
        print("\n=== Z3 voltage covers of C13(1,2,5) (sample) ===", flush=True)
        for v1, v2, v5 in itertools.product((0, 1, 2), repeat=3):
            if v1 == v2 == v5 == 0:
                continue
            vb = {1: v1, 2: v2, 5: v5}
            G = voltage_cover(n, base_S, 3, vb)
            r = profile(G, f"Z3cover v=({v1},{v2},{v5})")
            if r and r[0] == "WITNESS":
                best = r; break
            if r and isinstance(r[0], int) and (best is None or
                    (isinstance(best[0], int) and r[0] < best[0])):
                best = r

    print(f"\nBEST cover: {best[0] if best else None}", flush=True)
    if best and best[0] == "WITNESS":
        G = best[1]
        G2 = nx.convert_node_labels_to_integers(G)
        with open("forge_assault_cover_WITNESS.txt", "w") as f:
            f.write(f"# WITNESS via cover: n={G2.number_of_nodes()} m={G2.number_of_edges()}\n")
            for u, v in sorted(tuple(sorted(e)) for e in G2.edges()):
                f.write(f"{u} {v}\n")
        print("Saved forge_assault_cover_WITNESS.txt", flush=True)
