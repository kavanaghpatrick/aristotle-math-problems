#!/usr/bin/env python3
"""
forge_blitz_r2.py — kill-tests for forge round-2 candidates:
  forge-4: expander / high-vertex-connectivity δ≥6 substrate
  forge-5: rigid-diamond critical-edge replacement on the n=10 champion
  forge-6: tensor/lexicographic product with chromatic entanglement
All dual-verified with checkers.py.
"""
import itertools
import random
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def chi4(G):
    return (not is_k_colorable(G, 3)) and is_k_colorable(G, 4)


def is_4vc(G):
    if not chi4(G):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def reduce_to_4vc(G):
    H = nx.convert_node_labels_to_integers(G)
    if is_k_colorable(H, 3) or not is_k_colorable(H, 4):
        return None
    changed = True
    while changed:
        changed = False
        for v in list(H.nodes()):
            K = H.copy(); K.remove_node(v)
            if K.number_of_nodes() >= 4 and (not is_k_colorable(K, 3)) and is_k_colorable(K, 4):
                H = K; changed = True; break
    return nx.convert_node_labels_to_integers(H)


def report(G, name):
    G = nx.convert_node_labels_to_integers(G)
    degs = sorted(d for _, d in G.degree())
    if not chi4(G):
        c = 2 if is_k_colorable(G, 2) else (3 if is_k_colorable(G, 3) else ">=5")
        print(f"[{name}] n={G.number_of_nodes()} m={G.number_of_edges()} chi={c} "
              f"mindeg={degs[0] if degs else '-'}", flush=True)
        return None
    vc, _, bad = is_vertex_critical(G, 4)
    ce = critical_edges(G, 4)
    m = G.number_of_edges()
    kappa = nx.node_connectivity(G) if G.number_of_nodes() < 40 else "?"
    print(f"[{name}] n={G.number_of_nodes()} m={m} chi=4 mindeg={degs[0]} kappa={kappa} "
          f"vc={vc} noncrit_v={len(bad)} |E*|={len(ce)} redundant={m-len(ce)}", flush=True)
    if vc and len(ce) == 0:
        edges = [tuple(sorted(e)) for e in G.edges()]
        if checkers.is_erdos944_k_r1(edges, G.number_of_nodes(), 4):
            print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
            return ("W", G)
    return (len(ce) if vc else None, G)


# forge-4: expanders / high-connectivity random regular
def test_forge4():
    print("=== forge-4: expander / high-vertex-connectivity δ≥6 ===", flush=True)
    best = None
    rng = random.Random(0)
    for n in (12, 14, 16, 18, 20):
        for t in range(40):
            try:
                G = nx.random_regular_graph(6, n, seed=rng.randint(0, 10**9))
            except Exception:
                continue
            if not chi4(G):
                continue
            # high connectivity filter (expander proxy)
            if nx.node_connectivity(G) < 6:
                continue
            R = reduce_to_4vc(G)
            if R is None:
                continue
            vc, _, _ = is_vertex_critical(R, 4)
            ce = critical_edges(R, 4)
            if vc and (best is None or len(ce) < best[0]):
                best = (len(ce), R.copy())
                print(f"  n={n}: 4vc-reduced |E*|={len(ce)} (n={R.number_of_nodes()})", flush=True)
                if len(ce) == 0:
                    edges = [tuple(sorted(e)) for e in nx.convert_node_labels_to_integers(R).edges()]
                    if checkers.is_erdos944_k_r1(edges, R.number_of_nodes(), 4):
                        print("  *** WITNESS forge-4 ***", flush=True); return best
    print(f"  forge-4 best |E*|={best[0] if best else 'none (expanders rarely vertex-critical)'}", flush=True)
    return best


# forge-5: rigid diamond replacement
def test_forge5():
    print("\n=== forge-5: rigid-diamond critical-edge replacement on n=10 champion ===", flush=True)
    G0 = nx.convert_node_labels_to_integers(nx.from_graph6_bytes("ICpdbY{]_".encode()))
    ce0 = critical_edges(G0, 4)
    best = None
    # replace each critical edge uv by a diamond: remove uv, add x,y with u-x,u-y,v-x,v-y,x-y
    # (this forces u,v different via two paths u-x-v / u-y-v while x,y also adjacent)
    nxt = G0.number_of_nodes()
    H = G0.copy()
    newverts = []
    for (u, v) in ce0:
        if H.has_edge(u, v):
            H.remove_edge(u, v)
        x, y = nxt, nxt + 1; nxt += 2
        for a in (u, v):
            H.add_edge(a, x); H.add_edge(a, y)
        H.add_edge(x, y)
        newverts += [x, y]
    report(H, "all-diamonds (x,y deg-3 risk)")
    # also: link the diamond apexes pairwise to raise their degree above 3
    H2 = H.copy()
    for i in range(0, len(newverts) - 1, 2):
        if i + 2 < len(newverts):
            H2.add_edge(newverts[i], newverts[i + 2])
            H2.add_edge(newverts[i + 1], newverts[i + 3])
    r = report(H2, "diamonds+apex-links (raise deg)")
    if r and r[0] == "W":
        return r
    R = reduce_to_4vc(H2)
    if R is not None:
        r2 = report(R, "diamonds+links reduced-to-4vc")
        if r2 and isinstance(r2[0], int):
            best = (r2[0], r2[1])
    return best


# forge-6: products
def test_forge6():
    print("\n=== forge-6: tensor/lexicographic products ===", flush=True)
    best = None
    bases = {
        "C5[K2]": nx.lexicographic_product(nx.cycle_graph(5), nx.complete_graph(2)),
        "C7[K2]": nx.lexicographic_product(nx.cycle_graph(7), nx.complete_graph(2)),
        "K4xC5": nx.tensor_product(nx.complete_graph(4), nx.cycle_graph(5)),
        "C5[C5]": nx.lexicographic_product(nx.cycle_graph(5), nx.cycle_graph(5)),
        "W5[K2]": nx.lexicographic_product(nx.wheel_graph(5), nx.complete_graph(2)),
        "Groetzsch_x_K2": nx.tensor_product(nx.mycielskian(nx.cycle_graph(5)), nx.complete_graph(2)),
    }
    for name, G in bases.items():
        G = nx.convert_node_labels_to_integers(G)
        r = report(G, name)
        if r and r[0] == "W":
            return r
        if r and isinstance(r[0], int):
            R = reduce_to_4vc(G)
            if R is not None:
                r2 = report(R, name + " reduced")
                if r2 and r2[0] == "W":
                    return r2
                if r2 and isinstance(r2[0], int) and (best is None or r2[0] < best[0]):
                    best = (r2[0], r2[1])
    print(f"  forge-6 best |E*|={best[0] if best else 'none'}", flush=True)
    return best


if __name__ == "__main__":
    test_forge5()   # most targeted
    test_forge6()
    test_forge4()   # slowest
