"""
archivist: explicit reconstruction of the Jensen-Siggers 2012 construction
(SEMR 9:156-160), the closest-ever near-miss to Dirac k=4.

This builds H(m): a 4-VERTEX-CRITICAL graph with Theta(n^2) edges of which only
Theta(n) are critical. It is NOT a (4,1)-witness (it HAS critical edges), but it is
the exact near-miss structure forge wants to attack: a rigid complete-tripartite core
B = K_{2m,2m,2m} (ZERO critical edges) + a small "disagreement gadget" G(m) holding
ALL the critical edges.

Verified against the squad's shared checkers.py.

Construction (verbatim from the paper, /tmp/jensen_siggers.txt):
  B = B(m): complete tripartite K_{2m,2m,2m}, parts S1,S2,S3 (each 2m vertices).
  T = T(m): path x0 x1 ... x_{2m+1} + independent y1..ym, edges yi-x_{2i-1}, yi-x_{2i}.
  T'= T'(m): T(m) plus a leaf zi on each yi.
  G = G(m): star center v0, leaves v1,v2,v3; three copies Ti of T, three copies Ti' of T';
            Si := (copy of Y in Ti) U (copy of Z in Ti').
            Identify vi with x0 of Ti and Ti'; identify v_{i+1} (cyclic) with x_{2m+1} of Ti and Ti'.
  H' = B u G: identify B's Si with G's Si (i=1,2,3). Then H = a 4-critical subgraph of H'
            (remove vertices while staying non-3-colorable). By Lemma 4(ii) all of S1uS2uS3
            survive, and by Lemma 1 none of B's edges are critical.

We build H' directly and then take a vertex-critical core via greedy vertex deletion
(mirrors the paper's "remove vertices as long as not 3-colorable"), then verify.
"""
import sys
import networkx as nx
import checkers  # shared squad verifier (backtrack + SAT chi)


def build_T(m, prefix):
    """T(m): path x0..x_{2m+1}, independents y1..ym, edges yi-x_{2i-1}, yi-x_{2i}.
    Returns (G, x0_name, xlast_name, Y_names)."""
    G = nx.Graph()
    x = [f"{prefix}_x{i}" for i in range(2 * m + 2)]   # x0 .. x_{2m+1}
    y = [f"{prefix}_y{i}" for i in range(1, m + 1)]     # y1 .. ym
    G.add_nodes_from(x)
    G.add_nodes_from(y)
    for i in range(2 * m + 1):                          # path edges x_i - x_{i+1}
        G.add_edge(x[i], x[i + 1])
    for i in range(1, m + 1):                           # yi - x_{2i-1}, yi - x_{2i}
        G.add_edge(y[i - 1], x[2 * i - 1])
        G.add_edge(y[i - 1], x[2 * i])
    return G, x[0], x[2 * m + 1], y


def build_Tprime(m, prefix):
    """T'(m): T(m) + leaf zi on each yi. Returns (G, x0, xlast, Y, Z)."""
    G, x0, xlast, y = build_T(m, prefix)
    z = [f"{prefix}_z{i}" for i in range(1, m + 1)]
    for i in range(m):
        G.add_edge(y[i], z[i])
    return G, x0, xlast, y, z


def build_G(m):
    """G(m) of Construction 4. Returns (graph, [S1,S2,S3], [v0,v1,v2,v3])."""
    G = nx.Graph()
    v = [f"v{i}" for i in range(4)]                     # v0 center, v1,v2,v3 leaves
    G.add_nodes_from(v)
    for i in range(1, 4):
        G.add_edge(v[0], v[i])                          # star

    S = [set(), set(), set()]
    for i in range(3):                                  # i = 0,1,2  (paper's i=1,2,3)
        Ti, t_x0, t_xl, t_Y = build_T(m, f"T{i}")
        Tpi, p_x0, p_xl, p_Y, p_Z = build_Tprime(m, f"Tp{i}")
        G = nx.union(G, Ti)
        G = nx.union(G, Tpi)
        # identify vi with x0 of Ti and Ti'; v_{i+1 cyclic} with x_{2m+1} of Ti and Ti'
        vi = v[i + 1]                                   # v1,v2,v3
        vi1 = v[(i + 1) % 3 + 1]                         # cyclic next leaf
        G = nx.contracted_nodes(G, vi, t_x0, self_loops=False)
        G = nx.contracted_nodes(G, vi, p_x0, self_loops=False)
        G = nx.contracted_nodes(G, vi1, t_xl, self_loops=False)
        G = nx.contracted_nodes(G, vi1, p_xl, self_loops=False)
        # Si = copy of Y in Ti  U  copy of Z in Ti'
        S[i] = set(t_Y) | set(p_Z)
    return G, S, v


def build_B(m):
    """B(m) = complete tripartite K_{2m,2m,2m}. Returns (graph, [S1,S2,S3])."""
    G = nx.Graph()
    parts = [[f"B{p}_{j}" for j in range(2 * m)] for p in range(3)]
    for p in range(3):
        G.add_nodes_from(parts[p])
    for p in range(3):
        for q in range(p + 1, 3):
            for a in parts[p]:
                for b in parts[q]:
                    G.add_edge(a, b)
    return G, [set(parts[p]) for p in range(3)]


def build_Hprime(m):
    """H' = B u G, identifying B's Si with G's Si (matched by sorted order)."""
    Bg, B_S = build_B(m)
    Gg, G_S, v = build_G(m)
    H = nx.union(Bg, Gg, rename=("", ""))  # disjoint then contract
    # identify: pair up B's Si vertices with G's Si vertices one-to-one
    for i in range(3):
        bl = sorted(B_S[i])
        gl = sorted(G_S[i])
        assert len(bl) == len(gl), f"S{i} size mismatch B={len(bl)} G={len(gl)}"
        for bnode, gnode in zip(bl, gl):
            H = nx.contracted_nodes(H, bnode, gnode, self_loops=False)
    return H, [set(sorted(B_S[i])) for i in range(3)]


def vertex_critical_core(H, k):
    """Remove vertices greedily while G stays non-(k-1)-colorable (chi >= k).
    Mirrors the paper's '4-critical subgraph by removing vertices'."""
    H = H.copy()
    changed = True
    while changed:
        changed = False
        for x in list(H.nodes()):
            H2 = H.copy()
            H2.remove_node(x)
            if H2.number_of_nodes() == 0:
                continue
            if _chi(H2) >= k:
                H = H2
                changed = True
                break
    return H


def _chi(G):
    nodes = list(G.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    edges = [(idx[u], idx[w]) for u, w in G.edges()]
    return checkers.chi_bt(edges, len(nodes))


def verify(H, k):
    nodes = list(H.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    edges = [(idx[u], idx[w]) for u, w in H.edges()]
    n = len(nodes)
    chi_bt = checkers.chi_bt(edges, n)
    chi_sat = checkers.chromatic_number_sat(edges, n)
    vc = checkers.is_vertex_critical(edges, n, k)
    crit = [e for e in edges if checkers.chi_bt(checkers.edges_remove_edge(edges, e), n) < k]
    return dict(n=n, m_edges=len(edges), chi_bt=chi_bt, chi_sat=chi_sat,
                vertex_critical=vc, num_critical_edges=len(crit),
                no_critical_edge=(len(crit) == 0))


if __name__ == "__main__":
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    print(f"=== Jensen-Siggers H(m) construction, m={m} (k=4 near-miss) ===")
    Hp, S = build_Hprime(m)
    print(f"H' (B u G): n={Hp.number_of_nodes()}, edges={Hp.number_of_edges()}")
    print(f"  chi(H') = {_chi(Hp)} (expect >= 4)")
    H = vertex_critical_core(Hp, 4)
    print(f"4-critical core H: n={H.number_of_nodes()}, edges={H.number_of_edges()}")
    res = verify(H, 4)
    for kk, vv in res.items():
        print(f"  {kk}: {vv}")
