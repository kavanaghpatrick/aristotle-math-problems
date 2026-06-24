#!/usr/bin/env python3
"""
forge_js_full.py — EXACT reconstruction of Jensen-Siggers 2012 H = B ∪ G(m),
verbatim from constructions 1-4, then measure |E*| and attack the gadget.

Construction 1: B = K_{2m,2m,2m}, parts S1,S2,S3 of size 2m.
Construction 2: T(m): path x0 x1 ... x_{2m+1}; independent y1..ym; edges yi-x_{2i-1}, yi-x_{2i}.
   Y = {y1..ym}, Y+ = {x0, x_{2m+1}} ∪ Y.
Construction 3: T'(m): T(m) plus leaf zi adjacent to yi. Z={z1..zm}, Z+ = Z ∪ {x0,x_{2m+1}}.
Construction 4: G(m): star center v0, leaves v1,v2,v3. For i in [3], Ti=copy of T(m),
   Ti'=copy of T'(m). Si = (copy of Y in Ti) ∪ (copy of Z in Ti').
   Identify vi with x0 of Ti and Ti'.
   Identify v_{i+1} (cyclic: v_{3+1}=v1) with x_{2m+1} of Ti and Ti'.
H' = B ∪ G, identifying B's Si with G's Si (Si independent in G).
H = a 4-vertex-critical subgraph of H' (Lemma 4(ii) forces all Si into H).

NOTE on Si identification: G's Si has |Y|+|Z| = 2m vertices; B's Si has 2m
vertices. We identify them 1-1 (y_j of Ti <-> first m of B's Si; z_j of Ti' <->
last m of B's Si). This matches |Si|=2m on both sides.
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def build_T(m, tag):
    """T(m): returns graph + boundary handles. Nodes prefixed by tag."""
    G = nx.Graph()
    x = [(tag, "x", i) for i in range(2 * m + 2)]
    y = [(tag, "y", i) for i in range(1, m + 1)]
    for i in range(2 * m + 1):
        G.add_edge(x[i], x[i + 1])
    for i in range(1, m + 1):
        G.add_edge(y[i - 1], x[2 * i - 1])
        G.add_edge(y[i - 1], x[2 * i])
    return G, x, y


def build_Tprime(m, tag):
    G, x, y = build_T(m, tag)
    z = [(tag, "z", i) for i in range(1, m + 1)]
    for i in range(1, m + 1):
        G.add_edge(z[i - 1], y[i - 1])
    return G, x, y, z


def build_G(m):
    """Construction 4. Returns (graph, Si lists for i=1,2,3, v-handles)."""
    G = nx.Graph()
    v = [("v", i) for i in range(4)]  # v0,v1,v2,v3
    for i in (1, 2, 3):
        G.add_edge(v[0], v[i])
    Si = {1: [], 2: [], 3: []}
    for i in (1, 2, 3):
        # Ti
        Ti, xi, yi = build_T(m, f"T{i}")
        # Ti'
        Tip, xip, yip, zip_ = build_Tprime(m, f"Tp{i}")
        G = nx.compose(G, Ti)
        G = nx.compose(G, Tip)
        # identify vi with x0 of Ti and Ti'
        G = nx.contracted_nodes(G, v[i], xi[0], self_loops=False)
        G = nx.contracted_nodes(G, v[i], xip[0], self_loops=False)
        # identify v_{i+1} (cyclic) with x_{2m+1} of Ti and Ti'
        vi1 = v[1 + (i % 3)]  # i=1->v2, i=2->v3, i=3->v1
        G = nx.contracted_nodes(G, vi1, xi[2 * m + 1], self_loops=False)
        G = nx.contracted_nodes(G, vi1, xip[2 * m + 1], self_loops=False)
        # Si = copy of Y in Ti + copy of Z in Ti'
        Si[i] = list(yi) + list(zip_)
    return G, Si, v


def build_H(m):
    """H' = B ∪ G with B's Si identified to G's Si."""
    G, Si, v = build_G(m)
    B = nx.Graph()
    BS = {1: [(f"B", 1, j) for j in range(2 * m)],
          2: [(f"B", 2, j) for j in range(2 * m)],
          3: [(f"B", 3, j) for j in range(2 * m)]}
    for pi in (1, 2, 3):
        for pj in (1, 2, 3):
            if pi < pj:
                for a in BS[pi]:
                    for b in BS[pj]:
                        B.add_edge(a, b)
    H = nx.compose(G, B)
    # identify B's Si vertices with G's Si vertices (1-1)
    for i in (1, 2, 3):
        gverts = Si[i]            # 2m vertices (m y's + m z's)
        bverts = BS[i]            # 2m vertices
        for gv, bv in zip(gverts, bverts):
            H = nx.contracted_nodes(H, bv, gv, self_loops=False)
    return nx.convert_node_labels_to_integers(H)


def reduce_to_4vc(G):
    H = nx.convert_node_labels_to_integers(G)
    if is_k_colorable(H, 3) or not is_k_colorable(H, 4):
        return None
    changed = True
    while changed:
        changed = False
        for vtx in list(H.nodes()):
            K = H.copy(); K.remove_node(vtx)
            if K.number_of_nodes() >= 4 and (not is_k_colorable(K, 3)) and is_k_colorable(K, 4):
                H = K; changed = True; break
    return nx.convert_node_labels_to_integers(H)


if __name__ == "__main__":
    for m in (3, 4):
        print(f"\n=== Jensen-Siggers H(m={m}) ===", flush=True)
        Gm, Si, v = build_G(m)
        print(f"G(m): n={Gm.number_of_nodes()} m={Gm.number_of_edges()} "
              f"(expected n=21m+4={21*m+4}, m_edges=21m+6={21*m+6})", flush=True)
        H = build_H(m)
        print(f"H' = B∪G: n={H.number_of_nodes()} m={H.number_of_edges()}", flush=True)
        c3 = is_k_colorable(H, 3); c4 = is_k_colorable(H, 4)
        print(f"  3-colorable={c3} 4-colorable={c4} (want chi=4: F,T)", flush=True)
        if (not c3) and c4:
            R = reduce_to_4vc(H)
            if R:
                vc, _, bad = is_vertex_critical(R, 4)
                ce = critical_edges(R, 4)
                print(f"  4vc-subgraph H: n={R.number_of_nodes()} "
                      f"m={R.number_of_edges()} vc={vc} |E*|={len(ce)} "
                      f"frac={len(ce)/R.number_of_edges():.4f}", flush=True)
                # dual-check vertex-criticality
                edges = [tuple(sorted(e)) for e in nx.convert_node_labels_to_integers(R).edges()]
                print(f"  checkers vc={checkers.is_vertex_critical(edges, R.number_of_nodes(), 4)} "
                      f"no_crit_edge={checkers.has_no_critical_edge(edges, R.number_of_nodes(), 4)}",
                      flush=True)
