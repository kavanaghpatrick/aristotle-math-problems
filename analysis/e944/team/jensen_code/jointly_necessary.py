"""
THE LIVE FRONTIER: jointly-necessary mutual-cover gadgets.
Two WEAKENED J-S gadgets (each individually insufficient = 3-colorable with B),
sharing the SAME star + B, such that their UNION is 4-chromatic. If achievable with
vertex-criticality + reduced |E*|, it's the one regime not yet ruled out.

From js_joint.py: a single gadget needs ALL 3 transfer chains to force χ=4 with B
(1-2 chains → χ=3). So a 2-chain gadget is individually insufficient. Idea:
  G_a = chains {1,2}   (insufficient alone)
  G_b = chains {1,3} or {2,3} (insufficient alone)
sharing the SAME star v0,v1,v2,v3 and the SAME B. Does the union force χ=4?
And crucially: are the two gadgets MUTUALLY edge-covering (each edge of G_a backed
by a G_b-route, so χ(H-e)=4) while every vertex stays critical?

We test all pairs of 2-chain (and mixed) gadgets, sharing star + B, report:
  χ(B∪G_a), χ(B∪G_b) [must be 3 for 'jointly necessary'],
  χ(B∪G_a∪G_b) [must be 4],
  vertex-critical?, |E*|.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges
from jensen_siggers import build_B


def partial_gadget_shared_star(m, chains, star, tag, with_leaves=True):
    """Build a gadget on given `chains` using the SHARED star dict {0,1,2,3}->node.
    Internal vertices tagged. S_i (y/z) use shared ('S',i,..) labels."""
    G = nx.Graph()
    G.add_nodes_from(star.values())
    def vmod(i): return star[((i - 1) % 3) + 1]
    for i in chains:
        x0n, xen = vmod(i), vmod(i + 1)
        def xT(j):
            if j == 0: return x0n
            if j == 2*m+1: return xen
            return ("Tx", tag, i, j)
        for j in range(2*m+1): G.add_edge(xT(j), xT(j+1))
        for j in range(1, m+1):
            yj = ("S", i, "y", j); G.add_edge(yj, xT(2*j-1)); G.add_edge(yj, xT(2*j))
        if with_leaves:
            def xTp(j):
                if j == 0: return x0n
                if j == 2*m+1: return xen
                return ("Tpx", tag, i, j)
            for j in range(2*m+1): G.add_edge(xTp(j), xTp(j+1))
            for j in range(1, m+1):
                yj = ("Tpy", tag, i, j); G.add_edge(yj, xTp(2*j-1)); G.add_edge(yj, xTp(2*j))
                zj = ("S", i, "z", j); G.add_edge(zj, yj)
    return G


def assemble(m, chains_a, chains_b, with_leaves=True):
    star = {0: ("v", 0), 1: ("v", 1), 2: ("v", 2), 3: ("v", 3)}
    star_g = nx.Graph()
    for i in (1, 2, 3): star_g.add_edge(star[0], star[i])
    Ga = partial_gadget_shared_star(m, chains_a, star, "a", with_leaves)
    Gb = partial_gadget_shared_star(m, chains_b, star, "b", with_leaves)
    # B with part size 2m, S labels = y_1..y_m, z_1..z_m per part
    parts = 2 * m
    Bp = nx.complete_multipartite_graph(parts, parts, parts)
    rename = {}; idx = 0
    canon = {i: [("S", i, "y", j) for j in range(1, m+1)] + [("S", i, "z", j) for j in range(1, m+1)] for i in (1,2,3)}
    for i in (1, 2, 3):
        for k in range(parts):
            rename[idx] = canon[i][k]; idx += 1
    Bp = nx.relabel_nodes(Bp, rename)
    def union(*gs):
        H = nx.Graph()
        for g in gs:
            H.add_nodes_from(g.nodes()); H.add_edges_from(g.edges())
        return H
    BGa = union(Bp, star_g, Ga)
    BGb = union(Bp, star_g, Gb)
    BGab = union(Bp, star_g, Ga, Gb)
    return BGa, BGb, BGab


if __name__ == "__main__":
    print("=== JOINTLY-NECESSARY mutual-cover test (jensen) ===")
    print("Need: χ(B∪G_a)=3 AND χ(B∪G_b)=3 AND χ(B∪G_a∪G_b)=4 (jointly necessary)")
    m = 2
    chain_options = [(1,2), (1,3), (2,3), (1,), (2,), (3,)]
    for ca in chain_options:
        for cb in chain_options:
            if ca == cb: continue
            BGa, BGb, BGab = assemble(m, list(ca), list(cb))
            cha, chb, chab = chromatic_number(BGa), chromatic_number(BGb), chromatic_number(BGab)
            jointly_nec = (cha == 3 and chb == 3 and chab == 4)
            mark = ""
            if jointly_nec:
                vc = is_vertex_critical(BGab, 4)
                ce = critical_edges(BGab)
                mark = f"  <-- JOINTLY NECESSARY! vc={vc} |E*|={len(ce)}"
                if vc and len(ce) == 0: mark += "  *** WITNESS ***"
            if chab == 4 or jointly_nec:
                print(f"  G_a=chains{ca}, G_b=chains{cb}: χ(BGa)={cha} χ(BGb)={chb} χ(BGab)={chab}{mark}")
