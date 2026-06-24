"""
Jointly-necessary surgery, take 2: TWO gadgets sharing the SAME star
v0,v1,v2,v3, but with overlapping chain sets so EVERY chain is present in >=2
gadget copies (double-covered), making each chain's edges redundant while the
shared pigeonhole keeps the whole thing non-3-colorable.

Key from js_joint.py: a partial gadget on chains C (subset of {1,2,3}) glued to B
is non-3-colorable ONLY when C = {1,2,3} (all three). 1 or 2 chains -> chi=3.
So to force chi=4 we need all 3 chains PRESENT. To make every chain's edges
redundant, we need each chain present in >=2 vertex-disjoint copies sharing the
star + S_i.

Construction DC (double-cover): same star v0..v3; for each chain i in {1,2,3},
build TWO vertex-disjoint transfer gadgets (copy 'a' and copy 'b') between v_i and
v_{i+1}, both feeding the SAME S_i (y/z vertices shared with B). Then deleting one
edge of chain-i-copy-a leaves chain-i-copy-b still transferring -> chi stays 4 ->
edge non-critical. Test vertex-criticality: an internal vertex of copy-a, when
deleted, leaves copy-b doing the same job -> may NOT be critical -> the SAME
tension. We test whether it bites here too, or whether sharing the star/S_i
changes the outcome.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges, is_erdos944
from jensen_siggers import build_B


def build_doublecover(m, copies=("a", "b"), with_leaves=True):
    """Shared star; for each chain i, one transfer gadget per copy-tag, all sharing
    S_i (= B's part i). Returns (H, B2, gadget_edge_sets)."""
    G = nx.Graph()
    v0 = ("v", 0)
    G.add_node(v0)
    star = {}
    for i in (1, 2, 3):
        star[i] = ("v", i)
        G.add_node(star[i])
        G.add_edge(v0, star[i])

    def vmod(i):
        return star[((i - 1) % 3) + 1]

    gadget_edges = {}  # (chain i, copy) -> set of frozenset edges
    for i in (1, 2, 3):
        x0_node = vmod(i)
        xend_node = vmod(i + 1)
        for cp in copies:
            es = set()

            def add(u, w):
                G.add_edge(u, w)
                es.add(frozenset((u, w)))

            def xT(j):
                if j == 0:
                    return x0_node
                if j == 2 * m + 1:
                    return xend_node
                return ("Tx", cp, i, j)
            for j in range(0, 2 * m + 1):
                add(xT(j), xT(j + 1))
            for j in range(1, m + 1):
                yj = ("S", i, "y", j)
                G.add_node(yj)
                add(yj, xT(2 * j - 1))
                add(yj, xT(2 * j))
            if with_leaves:
                def xTp(j):
                    if j == 0:
                        return x0_node
                    if j == 2 * m + 1:
                        return xend_node
                    return ("Tpx", cp, i, j)
                for j in range(0, 2 * m + 1):
                    add(xTp(j), xTp(j + 1))
                for j in range(1, m + 1):
                    yj = ("Tpy", cp, i, j)
                    G.add_node(yj)
                    add(yj, xTp(2 * j - 1))
                    add(yj, xTp(2 * j))
                    zj = ("S", i, "z", j)
                    G.add_node(zj)
                    add(zj, yj)
            gadget_edges[(i, cp)] = es

    # glue B
    B, SB = build_B(m)
    canon = {p: [("S", p, "y", j) for j in range(1, m + 1)] +
                [("S", p, "z", j) for j in range(1, m + 1)] for p in (1, 2, 3)}
    rename = {}
    for p in (1, 2, 3):
        for k in range(2 * m):
            rename[SB[p][k]] = canon[p][k]
    B2 = nx.relabel_nodes(B, rename, copy=True)
    H = nx.Graph()
    for g in (B2, G):
        H.add_nodes_from(g.nodes())
        H.add_edges_from(g.edges())
    return H, B2, gadget_edges


if __name__ == "__main__":
    m = 2
    print(f"=== Double-cover (shared star, 2 copies per chain), m={m} ===")
    H, B2, ge = build_doublecover(m)
    print(f"H nodes={H.number_of_nodes()}, edges={H.number_of_edges()}")
    chi = chromatic_number(H)
    print(f"chi(H) = {chi}")
    if chi >= 4:
        # cheap: is it vertex-critical? test a few internal vertices first
        # an internal vertex of chain-1-copy-a:
        v = ("Tx", "a", 1, 1)
        T = H.copy(); T.remove_node(v)
        print(f"delete internal chain1-copyA vertex {v}: chi = {chromatic_number(T)} "
              f"(if 4 -> not critical -> not vertex-critical)")
        # full vertex-criticality + critical edges only if the cheap test passes
        vc = is_vertex_critical(H, 4)
        print(f"vertex-critical: {vc}")
        if vc:
            ce = critical_edges(H)
            Be = set(frozenset(e) for e in B2.edges())
            nb = sum(1 for e in [frozenset(x) for x in ce] if e in Be)
            print(f"|E*(H)| = {len(ce)}  (in B: {nb})")
            print(f"WITNESS: {is_erdos944(H,4)['is_witness']}")
