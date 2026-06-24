"""
Refined J-S surgery: JOINTLY-NECESSARY gadgets (the only escape from the
redundancy-vertex-criticality tension proven in js_surgery.py).

Goal: two gadgets G_a, G_b such that NEITHER B u G_a nor B u G_b is non-3-colorable
alone, but B u G_a u G_b IS, AND every gadget edge is covered by an obstruction
surviving its deletion. Then internal vertices can stay critical (each is needed
because removing it lets the JOINT obstruction collapse).

Approach: WEAKEN each gadget so it only forces "S_i bichromatic" for a SUBSET of
the (v_i, v_{i+1}) color-clash pairs. The J-S gadget uses all 3 transfer chains
T_1,T_2,T_3 (one per cyclic pair). A "partial" gadget using only SOME chains
forces the contradiction only for some pairs.

We build partial gadgets parameterized by WHICH chains (subset of {1,2,3}) are
present, test chi(B u partial) to find partials that are NOT independently
sufficient (chi=3), then look for complementary pairs whose union IS sufficient
(chi=4) -> jointly necessary candidate.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges
from jensen_siggers import build_B


def build_partial_gadget(m, tag, chains, with_leaves=True):
    """Build a gadget using only the transfer chains in `chains` (subset of {1,2,3}).
    chain i = the pair (T_i, T'_i) glued between v_i (x0) and v_{i+1} (x_{2m+1}).
    S_i is populated only by chains that touch it. with_leaves=False drops T'_i
    (the Z-side), giving an even weaker gadget."""
    G = nx.Graph()
    v0 = ("v", tag, 0)
    G.add_node(v0)
    star = {}
    for i in (1, 2, 3):
        star[i] = ("v", tag, i)
        G.add_node(star[i])
        G.add_edge(v0, star[i])

    def vmod(i):
        return star[((i - 1) % 3) + 1]

    Smap = {1: [], 2: [], 3: []}
    for i in chains:
        x0_node = vmod(i)
        xend_node = vmod(i + 1)

        def xT(j):
            if j == 0:
                return x0_node
            if j == 2 * m + 1:
                return xend_node
            return ("Tx", tag, i, j)
        for j in range(0, 2 * m + 1):
            G.add_edge(xT(j), xT(j + 1))
        for j in range(1, m + 1):
            yj = ("S", i, "y", j)
            G.add_node(yj)
            G.add_edge(yj, xT(2 * j - 1))
            G.add_edge(yj, xT(2 * j))
            Smap[i].append(yj)

        if with_leaves:
            def xTp(j):
                if j == 0:
                    return x0_node
                if j == 2 * m + 1:
                    return xend_node
                return ("Tpx", tag, i, j)
            for j in range(0, 2 * m + 1):
                G.add_edge(xTp(j), xTp(j + 1))
            for j in range(1, m + 1):
                yj = ("Tpy", tag, i, j)
                G.add_node(yj)
                G.add_edge(yj, xTp(2 * j - 1))
                G.add_edge(yj, xTp(2 * j))
                zj = ("S", i, "z", j)
                G.add_node(zj)
                G.add_edge(zj, yj)
                Smap[i].append(zj)
    return G, Smap


def glue_BG(m, gadgets):
    """Glue B(m) to a list of gadget graphs (each (G, Smap)), sharing S_i labels.
    B's S_i has 2m slots: y-slots then z-slots, matched positionally to whatever a
    gadget populates. We must ensure every B S_i vertex EXISTS in the union (B
    needs all 2m per part). Gadgets only populate S_i slots they touch; we still
    add ALL of B's S_i vertices and they participate in B's tripartite edges."""
    B, SB = build_B(m)
    # Canonical S labels (must match gadget labels): per part i, y_1..y_m then z_1..z_m
    canon = {i: [("S", i, "y", j) for j in range(1, m + 1)] +
                [("S", i, "z", j) for j in range(1, m + 1)] for i in (1, 2, 3)}
    rename = {}
    for i in (1, 2, 3):
        for k in range(2 * m):
            rename[SB[i][k]] = canon[i][k]
    B2 = nx.relabel_nodes(B, rename, copy=True)
    H = nx.Graph()
    H.add_nodes_from(B2.nodes())
    H.add_edges_from(B2.edges())
    for (G, _) in gadgets:
        H.add_nodes_from(G.nodes())
        H.add_edges_from(G.edges())
    return H, B2


def chi_of_partial(m, chains, with_leaves=True):
    G, S = build_partial_gadget(m, "p", chains, with_leaves)
    H, B2 = glue_BG(m, [(G, S)])
    return chromatic_number(H)


if __name__ == "__main__":
    m = 2
    print(f"=== Partial-gadget chi(B u partial) scan, m={m} ===")
    print("Which chain-subsets are INDEPENDENTLY SUFFICIENT (chi=4) vs not (chi=3)?")
    for wl in (True, False):
        print(f"-- with_leaves={wl} --")
        for r in (1, 2, 3):
            for chains in itertools.combinations((1, 2, 3), r):
                chi = chi_of_partial(m, chains, wl)
                tag = "SUFFICIENT(chi=4)" if chi >= 4 else f"insufficient(chi={chi})"
                print(f"  chains={chains}: {tag}")
