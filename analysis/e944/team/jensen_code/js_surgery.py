"""
Jensen-Siggers ASSAULT: characterize WHY each gadget edge is critical, then
SURGERY — overlay a second gadget so each critical edge gains a redundant
4-chromatic obstruction avoiding it, WITHOUT collapsing chi to 3 or breaking
vertex-criticality.

Background (verified in jensen_siggers.py, m=3):
  H = B(m) U G(m), 4-vertex-critical, chi=4. B's 108 edges = 0 critical.
  All 90 edges of G are critical. E* = E(G), connected + spanning.

Mechanism (paper Lemma 4(i)): H' is non-3-colorable because under ANY 3-coloring,
two of v1,v2,v3 share a color (all adjacent to v0), and the T_i/T'_i gadget on
that pair FORCES the corresponding S_i to be bichromatic, contradicting B's unique
3-coloring (which makes every S_i monochromatic). So G's role = "force some S_i
bichromatic." Each gadget edge is critical because removing it breaks the
color-transfer chain for one (v_i,v_{i+1}) pair, letting a 3-coloring slip through.

THE SURGERY IDEA (team-lead): the criticality of each G-edge is a SINGLE point of
failure in the color-transfer chain. If we overlay a SECOND independent gadget
G'(m) on the SAME B (sharing S_1,S_2,S_3 but with vertex-disjoint internal
gadgetry), then for an edge e in G, the graph H - e still contains G' which ALSO
forces some S_i bichromatic => H - e stays non-3-colorable => e becomes
NON-critical. The redundancy ("2nd independent obstruction") is exactly what the
shared-failure-mode analysis says k=4 lacks; two overlaid gadgets supply it.

RISK: overlaying G' may (a) break vertex-criticality (some vertex no longer
critical), or (b) make G' 's OWN edges critical (we just move the problem), or
(c) the two gadgets might not be independent (a single 3-coloring evades both
only if they constrain DIFFERENT pairs). We test all of this with the harness.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges, is_erdos944
from jensen_siggers import build_B, build_G, build_Hprime, four_critical_subgraph, Vstar


# ------- build G with a tag so two copies are vertex-disjoint except S_i -------
def build_G_tagged(m, tag):
    """Same as build_G but every INTERNAL (non-S_i, non-star?) node carries `tag`
    so two tagged copies are disjoint. The S_i vertices (y's and z's) and the star
    v0,v1,v2,v3 are SHARED across copies unless we also tag them.
    We tag EVERYTHING internal incl. star center (so each gadget has its own star),
    but KEEP S_i labels UNTAGGED so both copies attach to the same B.
    Decision: share v0,v1,v2,v3? The star vertices v_i are identified with x0/xend
    of the gadget paths. If we share them, the two gadgets share their boundary
    and may not be independent. So we give G' its OWN star v0',v1',v2',v3'. But
    then G' 's S_i must still be B's S_i. We keep S_i shared, star private.
    """
    from jensen_siggers import Ty, Tpz
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
    for i in (1, 2, 3):
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
            yj = ("S", i, "y", j)          # UNTAGGED -> shared S_i
            G.add_node(yj)
            G.add_edge(yj, xT(2 * j - 1))
            G.add_edge(yj, xT(2 * j))
            Smap[i].append(yj)

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
            zj = ("S", i, "z", j)          # UNTAGGED -> shared S_i
            G.add_node(zj)
            G.add_edge(zj, yj)
            Smap[i].append(zj)
    return G, Smap


def build_double_Hprime(m):
    """H'' = B(m) U G_a(m) U G_b(m), both gadgets sharing S_1,S_2,S_3 of B but
    otherwise vertex-disjoint (own stars + own internal paths)."""
    B, SB = build_B(m)
    Ga, SGa = build_G_tagged(m, "a")
    Gb, SGb = build_G_tagged(m, "b")
    # S_i labels are identical across B-target, Ga, Gb (we use the same ("S",i,..)
    # scheme). Relabel B's S_i onto the shared scheme.
    rename = {}
    for i in (1, 2, 3):
        for k in range(2 * m):
            rename[SB[i][k]] = SGa[i][k]  # SGa and SGb use identical S labels
    B2 = nx.relabel_nodes(B, rename, copy=True)
    H = nx.Graph()
    for g in (B2, Ga, Gb):
        H.add_nodes_from(g.nodes())
        H.add_edges_from(g.edges())
    return H, B2, Ga, Gb


def analyze(m):
    print(f"==== DOUBLE-GADGET surgery, m={m} ====")
    Hpp, B2, Ga, Gb = build_double_Hprime(m)
    print(f"  H'' nodes={Hpp.number_of_nodes()}, edges={Hpp.number_of_edges()}")
    chi = chromatic_number(Hpp)
    print(f"  chi(H'') = {chi}  (need >=4)")
    if chi < 4:
        print("  COLLAPSED to 3-colorable -- gadgets not independent enough. STOP.")
        return
    H = four_critical_subgraph(Hpp)
    print(f"  H (4-crit subgraph): n={H.number_of_nodes()}, m={H.number_of_edges()}")
    print(f"  chi={chromatic_number(H)}, vertex-critical={is_vertex_critical(H,4)}")
    ce = critical_edges(H)
    Be = set(frozenset(e) for e in B2.edges())
    Gae = set(frozenset(e) for e in Ga.edges())
    Gbe = set(frozenset(e) for e in Gb.edges())
    cef = [frozenset(e) for e in ce]
    nb = sum(1 for e in cef if e in Be)
    na = sum(1 for e in cef if e in Gae)
    nbb = sum(1 for e in cef if e in Gbe)
    print(f"  |E*(H)| = {len(ce)}   (in B: {nb}, in G_a: {na}, in G_b: {nbb})")
    print(f"  --> single-gadget had 90 critical; double-gadget has {len(ce)}")
    rep = is_erdos944(H, 4)
    print(f"  WITNESS? {rep['is_witness']}")
    return H, ce


if __name__ == "__main__":
    analyze(3)
