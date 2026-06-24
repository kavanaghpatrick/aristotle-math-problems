"""
Jensen-Siggers 2012 k=4 construction, built EXACTLY from the paper
(T. Jensen & M. Siggers, SEMR 9 (2012) 156-160; full text /tmp/jensen_siggers.txt).

This is the CLOSEST published result to Dirac k=4: a 4-vertex-critical graph H
with |E*(H)| = O(n) critical edges among Theta(n^2) total. ALL critical edges
live in the gadget part G(m); the blowup B(m)=K_{2m,2m,2m} contributes ZERO.

Constructions (verbatim):
  B(m): complete tripartite K_{2m,2m,2m}, parts S1,S2,S3 (2m vertices each).
  T(m): path x0 x1 ... x_{2m+1}; independent y1..ym; edges yi-x_{2i-1}, yi-x_{2i}.
        Y={y1..ym}, Y+={x0,x_{2m+1}} U Y.  (3m+2 vertices, 3m+1 edges)
  T'(m): T(m) + leaf zi adjacent to yi.  Z={z1..zm}, Z+=Z U {x0,x_{2m+1}}.
        (4m+2 vertices, 4m+1 edges)
  G(m): star center v0, leaves v1,v2,v3; copies T_i, T'_i for i in [3].
        S_i = (copy of Y in T_i) U (copy of Z in T'_i).   [2m vertices]
        Gluing (indices mod 3, v_4=v_1):
          v_i   == x0       of T_i and T'_i
          v_{i+1} == x_{2m+1} of T_i and T'_i
        (n=21m+4 vertices, 21m+6 edges)
  H' = B(m) U G(m), identifying S_i(B) with S_i(G).  H'=not 3-colorable (chi>=4).
  H  = 4-critical-by-VERTEX-removal subgraph of H' (remove vertices while staying
       non-3-colorable). chi=4, vertex-critical, E*(H) subset E(G).

We build with explicit, namespaced node labels so the gluing is unambiguous, then
hand the result to harness.py for verification (chi, vertex-crit, critical edges).
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges, is_erdos944


# ---- node label helpers (unique, human-readable) ----
def Bnode(part, idx):           # part in {1,2,3}, idx in [0,2m)
    return ("B", part, idx)

def Tx(i, j):                   # x_j of copy T_i (i in 1..3), j in 0..2m+1
    return ("Tx", i, j)

def Ty(i, j):                   # y_j of copy T_i (j in 1..m) -- lives in S_i
    return ("S", i, "y", j)

def Tpx(i, j):                  # x_j of copy T'_i
    return ("Tpx", i, j)

def Tpy(i, j):                  # y_j of copy T'_i
    return ("Tpy", i, j)

def Tpz(i, j):                  # z_j of copy T'_i (leaf on y_j) -- lives in S_i
    return ("S", i, "z", j)

def Vstar(i):                   # star vertices v0,v1,v2,v3
    return ("v", i)


def build_B(m):
    """K_{2m,2m,2m}. Returns (graph, S) where S[i] = list of part-i vertices
    (i in 1,2,3). S_i has 2m vertices: first m are the 'Y slots', last m 'Z slots'
    -- but in B they are just an independent set; the Y/Z split matters only at
    the identification with G."""
    G = nx.Graph()
    S = {1: [], 2: [], 3: []}
    for part in (1, 2, 3):
        for idx in range(2 * m):
            v = Bnode(part, idx)
            G.add_node(v)
            S[part].append(v)
    for p in (1, 2, 3):
        for q in (1, 2, 3):
            if p < q:
                for u in S[p]:
                    for w in S[q]:
                        G.add_edge(u, w)
    return G, S


def build_G(m):
    """Construction 4. Returns (graph, Smap) where Smap[i] is the list of the 2m
    vertices forming S_i in G: the m y-vertices of T_i then the m z-vertices of T'_i.
    The star/path internal vertices x_j (j in 1..2m) are NOT in any S_i.
    Boundary identifications:
       v_i      plays x0       in T_i and T'_i
       v_{i+1}  plays x_{2m+1} in T_i and T'_i      (v_4 = v_1)
    v0 is the star center adjacent to v1,v2,v3.
    """
    G = nx.Graph()
    # star
    v0 = Vstar(0)
    G.add_node(v0)
    for i in (1, 2, 3):
        G.add_node(Vstar(i))
        G.add_edge(v0, Vstar(i))

    def vmod(i):
        # v_1,v_2,v_3 cyclic; v_4 -> v_1
        return Vstar(((i - 1) % 3) + 1)

    Smap = {1: [], 2: [], 3: []}

    for i in (1, 2, 3):
        x0_node = vmod(i)        # x0 of T_i and T'_i  == v_i
        xend_node = vmod(i + 1)  # x_{2m+1}            == v_{i+1}

        # ---- copy T_i ----
        # path x0 x1 ... x_{2m+1}; x0=x0_node, x_{2m+1}=xend_node, internal x_1..x_2m fresh
        def xT(j):
            if j == 0:
                return x0_node
            if j == 2 * m + 1:
                return xend_node
            return Tx(i, j)
        for j in range(0, 2 * m + 1):
            G.add_edge(xT(j), xT(j + 1))
        for j in range(1, m + 1):
            yj = Ty(i, j)
            G.add_node(yj)
            G.add_edge(yj, xT(2 * j - 1))
            G.add_edge(yj, xT(2 * j))
            Smap[i].append(yj)   # y-part of S_i

        # ---- copy T'_i ----
        def xTp(j):
            if j == 0:
                return x0_node
            if j == 2 * m + 1:
                return xend_node
            return Tpx(i, j)
        for j in range(0, 2 * m + 1):
            G.add_edge(xTp(j), xTp(j + 1))
        for j in range(1, m + 1):
            yj = Tpy(i, j)
            G.add_node(yj)
            G.add_edge(yj, xTp(2 * j - 1))
            G.add_edge(yj, xTp(2 * j))
            zj = Tpz(i, j)       # leaf on y_j
            G.add_node(zj)
            G.add_edge(zj, yj)
            Smap[i].append(zj)   # z-part of S_i

    return G, Smap


def build_Hprime(m):
    """H' = B(m) U G(m) with S_i(B) identified with S_i(G).
    We build B and G separately, then identify by RENAMING B's S_i vertices onto
    G's S_i vertices (same 2m-element list, positionally)."""
    B, SB = build_B(m)
    Gg, SG = build_G(m)
    # rename map: B's S_i[k]  ->  G's S_i[k]
    rename = {}
    for i in (1, 2, 3):
        assert len(SB[i]) == len(SG[i]) == 2 * m, (len(SB[i]), len(SG[i]), 2 * m)
        for k in range(2 * m):
            rename[SB[i][k]] = SG[i][k]
    B2 = nx.relabel_nodes(B, rename, copy=True)
    # union (shared S_i nodes merge automatically since labels now coincide)
    H = nx.Graph()
    H.add_edges_from(B2.edges())
    H.add_edges_from(Gg.edges())
    H.add_nodes_from(B2.nodes())
    H.add_nodes_from(Gg.nodes())
    return H, SG, B2, Gg


def four_critical_subgraph(Hprime):
    """Remove vertices greedily as long as the graph stays NON-3-colorable.
    Result is 4-vertex-critical (every remaining vertex deletion makes it
    3-colorable)."""
    H = Hprime.copy()
    assert chromatic_number(H) >= 4, "H' must be >=4-chromatic"
    changed = True
    while changed:
        changed = False
        for v in list(H.nodes()):
            T = H.copy()
            T.remove_node(v)
            if chromatic_number(T) >= 4:
                H = T
                changed = True
                break
    return H


if __name__ == "__main__":
    for m in (3,):
        print(f"==== Jensen-Siggers m={m} ====")
        Hp, SG, B2, Gg = build_Hprime(m)
        nB = sum(len(SG[i]) for i in (1, 2, 3))
        print(f"  B(m): K_{{{2*m},{2*m},{2*m}}}, parts merged into S_i")
        print(f"  G(m): n_expected=21m+4={21*m+4}, m_edges_expected=21m+6={21*m+6}")
        print(f"        actual G nodes={Gg.number_of_nodes()}, edges={Gg.number_of_edges()}")
        print(f"  H' nodes={Hp.number_of_nodes()}, edges={Hp.number_of_edges()}")
        chi_Hp = chromatic_number(Hp)
        print(f"  chi(H') = {chi_Hp}  (expect >= 4)")
        if chi_Hp >= 4:
            H = four_critical_subgraph(Hp)
            print(f"  H (4-crit subgraph): n={H.number_of_nodes()}, m={H.number_of_edges()}")
            print(f"  chi(H) = {chromatic_number(H)}")
            print(f"  vertex-critical: {is_vertex_critical(H, 4)}")
            ce = critical_edges(H)
            print(f"  #critical edges |E*(H)| = {len(ce)}  (paper: O(n), <= 21m+6={21*m+6})")
