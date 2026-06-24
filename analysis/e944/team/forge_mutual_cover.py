#!/usr/bin/env python3
"""
forge_mutual_cover.py — test jensen's "two gadgets covering each other's critical
edges" idea on the Jensen-Siggers substrate.

J-S: B = K_{2m,2m,2m} (0 critical edges, rigid 3-coloring) + ONE disagreement
gadget G forcing >=1 part bichromatic (chi=4). ALL critical edges live in G.

jensen's hypothesis: a SECOND gadget G' that covers G's critical edges (and vice
versa) supplies the "second independent obstruction" missing at k=4 — IF the two
are entangled (share vertices) not separable (my earlier parallelization added a
separable copy, which trimmed away).

TEST: build H = B + G_A + G_B, where G_A and G_B are two disagreement gadgets
attached to the SAME core B but via DIFFERENT structure, sharing some vertices.
Measure: chi, vertex-criticality, |E*|. Does |E*| drop below the single-gadget
value? Does any edge of G_A become redundant (covered by G_B)?

We use the verified J-S builders from forge_js_full. We attach a SECOND gadget by
building a second G(m) on the same B (re-using B's Si) but with the star leaves
permuted (so it forces a DIFFERENT pair of parts bichromatic), and identify the
two gadgets' Si into B's Si (shared core = entanglement through the core).
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers
from forge_js_full import build_T, build_Tprime, reduce_to_4vc


def build_G_variant(m, tag, leaf_perm):
    """Construction 4 with a tag namespace and a permutation of which leaf maps
    to which part (to force a different disagreement pattern)."""
    G = nx.Graph()
    v = [(tag, "v", i) for i in range(4)]
    for i in (1, 2, 3):
        G.add_edge(v[0], v[i])
    Si = {1: [], 2: [], 3: []}
    for i in (1, 2, 3):
        Ti, xi, yi = build_T(m, f"{tag}_T{i}")
        Tip, xip, yip, zip_ = build_Tprime(m, f"{tag}_Tp{i}")
        G = nx.compose(G, Ti); G = nx.compose(G, Tip)
        G = nx.contracted_nodes(G, v[i], xi[0], self_loops=False)
        G = nx.contracted_nodes(G, v[i], xip[0], self_loops=False)
        vi1 = v[1 + (i % 3)]
        G = nx.contracted_nodes(G, vi1, xi[2 * m + 1], self_loops=False)
        G = nx.contracted_nodes(G, vi1, xip[2 * m + 1], self_loops=False)
        # map this gadget's S_i to core part leaf_perm[i]
        Si[leaf_perm[i]] = list(yi) + list(zip_)
    return G, Si, v


def build_H_two_gadget(m, perm_b):
    """B = K_{2m,2m,2m}; attach G_A (identity perm) and G_B (perm_b), both
    sharing B's parts (entanglement through the core)."""
    GA, SiA, vA = build_G_variant(m, "A", {1: 1, 2: 2, 3: 3})
    GB, SiB, vB = build_G_variant(m, "B", perm_b)
    # core B
    Bg = nx.Graph()
    BS = {i: [("B", i, j) for j in range(2 * m)] for i in (1, 2, 3)}
    for pi in (1, 2, 3):
        for pj in (1, 2, 3):
            if pi < pj:
                for a in BS[pi]:
                    for b in BS[pj]:
                        Bg.add_edge(a, b)
    H = nx.compose(GA, GB)
    H = nx.compose(H, Bg)
    # identify both gadgets' Si into B's Si (shared core)
    for i in (1, 2, 3):
        for gv, bv in zip(SiA[i], BS[i]):
            H = nx.contracted_nodes(H, bv, gv, self_loops=False)
    for i in (1, 2, 3):
        # SiB[i] may already partly be identified; identify remaining
        for gv, bv in zip(SiB[i], BS[i]):
            if H.has_node(gv) and H.has_node(bv) and gv != bv:
                H = nx.contracted_nodes(H, bv, gv, self_loops=False)
    return nx.convert_node_labels_to_integers(H)


def analyze(H, name):
    c3 = is_k_colorable(H, 3); c4 = is_k_colorable(H, 4)
    if c3 or not c4:
        print(f"[{name}] n={H.number_of_nodes()} m={H.number_of_edges()} "
              f"chi={'<=3' if c3 else '>=5'}", flush=True)
        return None
    R = reduce_to_4vc(H)
    if R is None:
        print(f"[{name}] no 4vc reduction", flush=True); return None
    ce = critical_edges(R, 4)
    vc, _, _ = is_vertex_critical(R, 4)
    m = R.number_of_edges()
    print(f"[{name}] 4vc: n={R.number_of_nodes()} m={m} vc={vc} "
          f"|E*|={len(ce)} frac={len(ce)/m:.3f}", flush=True)
    if vc and len(ce) == 0:
        edges = [tuple(sorted(e)) for e in nx.convert_node_labels_to_integers(R).edges()]
        if checkers.is_erdos944_k_r1(edges, R.number_of_nodes(), 4):
            print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
            return ("W", R)
    return (len(ce), R)


if __name__ == "__main__":
    m = 2  # smallest for tractability (J-S needs m>=3 for unique-coloring lemma,
           # but we test the MECHANISM; chi is verified exactly regardless)
    print("=== Single-gadget baseline (m=2,3) ===", flush=True)
    from forge_js_full import build_H
    for mm in (2, 3):
        analyze(build_H(mm), f"JS single m={mm}")

    print("\n=== Two mutually-covering gadgets, various 2nd-gadget perms ===", flush=True)
    # perms of {1,2,3} for gadget B (different disagreement target)
    for perm in [{1:2,2:3,3:1}, {1:3,2:1,3:2}, {1:2,2:1,3:3}, {1:1,2:3,3:2}]:
        analyze(build_H_two_gadget(m, perm), f"two-gadget m={m} perm={perm}")
