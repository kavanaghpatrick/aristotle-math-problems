#!/usr/bin/env python3
"""
forge_js_attack.py — attack the Jensen-Siggers gadget G to reduce |E*| below
J-S's Theorem-1 level (frac of critical edges), ideally toward 0.

Strategy: PARALLELIZE the disagreement gadget. J-S forces ">=1 Si bichromatic"
via a SINGLE transfer path T_i per part. If a gadget edge e is critical, then
deleting e lets a 3-coloring "escape" (all Si monochromatic). If we provide a
SECOND, edge-disjoint transfer structure enforcing the same disagreement, then
deleting any single edge of one copy leaves the other intact => that edge
non-critical.

We implement: build H(m), then for each part add a SECOND independent copy of
T_i and T_i' (different internal vertices, same boundary identifications). This
doubles the gadget. Measure |E*| of the 4vc-reduction. If doubling reduces |E*|
(critical edges that gained a backup), iterate / triple.

Also probe wall's spanning-E* conjecture: is E* connected? spanning? (report).
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers
from forge_js_full import build_T, build_Tprime, reduce_to_4vc


def build_G_parallel(m, copies=1):
    """Construction 4 with `copies` parallel T_i / T_i' per part."""
    G = nx.Graph()
    v = [("v", i) for i in range(4)]
    for i in (1, 2, 3):
        G.add_edge(v[0], v[i])
    Si = {1: [], 2: [], 3: []}
    for i in (1, 2, 3):
        vi1 = v[1 + (i % 3)]
        for cp in range(copies):
            Ti, xi, yi = build_T(m, f"T{i}_{cp}")
            Tip, xip, yip, zip_ = build_Tprime(m, f"Tp{i}_{cp}")
            G = nx.compose(G, Ti)
            G = nx.compose(G, Tip)
            G = nx.contracted_nodes(G, v[i], xi[0], self_loops=False)
            G = nx.contracted_nodes(G, v[i], xip[0], self_loops=False)
            G = nx.contracted_nodes(G, vi1, xi[2 * m + 1], self_loops=False)
            G = nx.contracted_nodes(G, vi1, xip[2 * m + 1], self_loops=False)
            Si[i] += list(yi) + list(zip_)
    return G, Si, v


def build_H_parallel(m, copies=1):
    G, Si, v = build_G_parallel(m, copies)
    B = nx.Graph()
    # B's Si must match |Si[i]| size
    BS = {}
    for i in (1, 2, 3):
        BS[i] = [("B", i, j) for j in range(len(Si[i]))]
    for pi in (1, 2, 3):
        for pj in (1, 2, 3):
            if pi < pj:
                for a in BS[pi]:
                    for b in BS[pj]:
                        B.add_edge(a, b)
    H = nx.compose(G, B)
    for i in (1, 2, 3):
        for gv, bv in zip(Si[i], BS[i]):
            H = nx.contracted_nodes(H, bv, gv, self_loops=False)
    return nx.convert_node_labels_to_integers(H)


def analyze(H, name):
    c3 = is_k_colorable(H, 3); c4 = is_k_colorable(H, 4)
    print(f"[{name}] n={H.number_of_nodes()} m={H.number_of_edges()} "
          f"3col={c3} 4col={c4}", flush=True)
    if c3 or not c4:
        return None
    R = reduce_to_4vc(H)
    if R is None:
        print("  (no 4vc reduction)", flush=True); return None
    ce = critical_edges(R, 4)
    vc, _, _ = is_vertex_critical(R, 4)
    frac = len(ce) / R.number_of_edges() if R.number_of_edges() else 0
    # E* connectivity probe
    Estar = nx.Graph(); Estar.add_edges_from(ce)
    conn = nx.is_connected(Estar) if Estar.number_of_nodes() else True
    spanning = (Estar.number_of_nodes() == R.number_of_nodes()) if ce else False
    print(f"  4vc: n={R.number_of_nodes()} m={R.number_of_edges()} vc={vc} "
          f"|E*|={len(ce)} frac={frac:.4f} E*_connected={conn} "
          f"E*_spanning={spanning} (E* touches {Estar.number_of_nodes()} verts)",
          flush=True)
    if vc and len(ce) == 0:
        G2 = nx.convert_node_labels_to_integers(R)
        edges = [tuple(sorted(e)) for e in G2.edges()]
        if checkers.is_erdos944_k_r1(edges, G2.number_of_nodes(), 4):
            print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
            return ("WITNESS", R)
    return (len(ce), R)


if __name__ == "__main__":
    print("=== Baseline single-copy J-S (m=3) ===", flush=True)
    analyze(build_H_parallel(3, copies=1), "JS m=3 copies=1")

    print("\n=== Parallelized gadget (m=3, 2 copies) ===", flush=True)
    analyze(build_H_parallel(3, copies=2), "JS m=3 copies=2")

    print("\n=== Parallelized gadget (m=3, 3 copies) ===", flush=True)
    analyze(build_H_parallel(3, copies=3), "JS m=3 copies=3")
