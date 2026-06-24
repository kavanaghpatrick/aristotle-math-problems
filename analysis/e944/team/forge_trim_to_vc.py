#!/usr/bin/env python3
"""
forge_trim_to_vc.py — take the 0-critical-edge (but NOT vertex-critical) biwheel/
double-cover graphs and trim them to vertex-critical, measuring how many critical
edges REAPPEAR. This quantifies the core tension:
    edge-redundancy (fat graph) <-> vertex-criticality (lean graph).

A non-vertex-critical 4-chromatic graph G has 'removable' vertices (G-v still
chi=4). We can delete removable vertices to head toward vertex-critical. Each
deletion REMOVES obstruction redundancy, potentially turning redundant edges
critical. We explore ALL trimming orders (BFS over removable-vertex deletions)
and report the minimum critical-edge count over all 4-vertex-critical graphs
reachable by trimming.

If ANY trimming order reaches vertex-critical with 0 critical edges -> WITNESS.
"""
import itertools
from collections import deque
import networkx as nx
from forge_verify import (is_k_colorable, is_vertex_critical, critical_edges,
                          is_e944_witness)


def odd_wheel(t):
    G = nx.cycle_graph(2 * t + 1)
    hub = 2 * t + 1
    for v in range(2 * t + 1):
        G.add_edge(hub, v)
    return G


def biwheel(cycle_nodes, drop=None):
    n = len(cycle_nodes)
    G = nx.Graph()
    for i in range(n):
        G.add_edge(cycle_nodes[i], cycle_nodes[(i + 1) % n])
    for v in cycle_nodes:
        G.add_edge("a", v); G.add_edge("b", v)
    G.add_edge("a", "b")
    if drop:
        for (ap, v) in drop:
            if G.has_edge(ap, v):
                G.remove_edge(ap, v)
    return G


def removable_vertices(G):
    """vertices v with chi(G-v) still == 4 (i.e. NOT critical)."""
    out = []
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if H.number_of_nodes() == 0:
            continue
        if not is_k_colorable(H, 3):  # H still needs >=4 colors
            # but also H must be 4-colorable; if chi(H)>=5 it's weird, skip
            if is_k_colorable(H, 4):
                out.append(v)
    return out


def is_4vc(G):
    if is_k_colorable(G, 3) or not is_k_colorable(G, 4):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def trim_search(G0, max_states=4000):
    """
    BFS over trimming (delete removable vertices). Track min critical edges among
    all 4-vertex-critical graphs encountered. Returns (best_nc, best_graph).
    """
    seen = set()
    start = nx.convert_node_labels_to_integers(G0)
    q = deque([start])
    best = None
    states = 0
    while q and states < max_states:
        G = q.popleft()
        key = nx.weisfeiler_lehman_graph_hash(G)
        if key in seen:
            continue
        seen.add(key)
        states += 1
        if not is_k_colorable(G, 3) and is_k_colorable(G, 4):
            if is_4vc(G):
                nc = len(critical_edges(G, 4))
                if best is None or nc < best[0]:
                    best = (nc, G.copy())
                    print(f"  4vc reached: n={G.number_of_nodes()} "
                          f"m={G.number_of_edges()} critical_edges={nc}", flush=True)
                    if nc == 0:
                        print("  *** WITNESS ***", flush=True)
                        return best
                # vertex-critical: cannot trim further, it's a leaf
                continue
        # not yet vertex-critical: expand by deleting each removable vertex
        for v in removable_vertices(G):
            H = G.copy(); H.remove_node(v)
            q.append(nx.convert_node_labels_to_integers(H))
    return best


if __name__ == "__main__":
    candidates = [
        ("biwheel(C7)-asym a0,b1", biwheel(list(range(7)), drop=[("a",0),("b",1)])),
        ("biwheel(C9)-asym a0,b1", biwheel(list(range(9)), drop=[("a",0),("b",1)])),
        ("biwheel(C7)-asym a0,b3", biwheel(list(range(7)), drop=[("a",0),("b",3)])),
        ("biwheel(C9)-asym a0,b4", biwheel(list(range(9)), drop=[("a",0),("b",4)])),
        ("biwheel(C11)-asym a0,b1", biwheel(list(range(11)), drop=[("a",0),("b",1)])),
        ("biwheel(C11)-asym a0,b5", biwheel(list(range(11)), drop=[("a",0),("b",5)])),
    ]
    overall = None
    for name, G in candidates:
        print(f"=== Trimming {name} (n={G.number_of_nodes()} m={G.number_of_edges()}) ===", flush=True)
        best = trim_search(G)
        if best is None:
            print("  (no 4-vertex-critical graph reachable by trimming)", flush=True)
        else:
            print(f"  best for {name}: critical_edges={best[0]} "
                  f"n={best[1].number_of_nodes()}", flush=True)
            if overall is None or best[0] < overall[0]:
                overall = (best[0], best[1].copy(), name)
        if overall and overall[0] == 0:
            break
    if overall:
        print(f"\nOVERALL best: critical_edges={overall[0]} from {overall[2]} "
              f"n={overall[1].number_of_nodes()} m={overall[1].number_of_edges()}", flush=True)
        if overall[0] == 0:
            is_e944_witness(overall[1])
            with open("forge_WITNESS.txt", "w") as f:
                f.write(f"# E944 WITNESS n={overall[1].number_of_nodes()} "
                        f"m={overall[1].number_of_edges()}\n")
                for u, v in sorted(tuple(sorted(e)) for e in overall[1].edges()):
                    f.write(f"{u} {v}\n")
            print("Saved forge_WITNESS.txt", flush=True)
