#!/usr/bin/env python3
"""
forge_kneser_trim.py — trim the dense 0-critical-edge Kneser graphs K(6,2)/K(8,3)
toward vertex-criticality, tracking min |E*| at the boundary. Also try
INTERMEDIATE graphs between K(2k+2,k) and the Schrijver subgraph SG(2k+2,k).

K(6,2): 6-regular, n=15, χ=4, 0 critical edges, NOT vertex-critical (all 15
removable). SG(6,2): the canonical vertex-critical subgraph, but |E*|=15/18.
Question: is there a vertex-critical subgraph of K(6,2) with FEWER critical edges
than SG — ideally 0 (witness)?

Approach:
 (A) BFS/greedy trim of K(6,2): delete removable vertices in many orders,
     preferring orders that KEEP |E*|=0 as long as possible; record min |E*| at
     each vertex-critical boundary reached.
 (B) Edge-subset interpolation: K(6,2) ⊇ H ⊇ SG(6,2). Try removing vertex subsets
     of K(6,2) other than the Schrijver "unstable" set.
All dual-verified.
"""
import itertools
import random
from collections import deque
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def kneser(n, k):
    V = list(itertools.combinations(range(n), k))
    G = nx.Graph(); G.add_nodes_from(V)
    for a, b in itertools.combinations(V, 2):
        if not (set(a) & set(b)):
            G.add_edge(a, b)
    return G


def chi4(G):
    return (not is_k_colorable(G, 3)) and is_k_colorable(G, 4)


def removable(G):
    out = []
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if H.number_of_nodes() >= 4 and chi4(H):
            out.append(v)
    return out


def crit(G):
    return len(critical_edges(G, 4))


def is_4vc(G):
    return chi4(G) and not removable(G)


def dual_witness(G):
    if not is_4vc(G) or crit(G) != 0:
        return False
    G2 = nx.convert_node_labels_to_integers(G)
    edges = [tuple(sorted(e)) for e in G2.edges()]
    return checkers.is_erdos944_k_r1(edges, G2.number_of_nodes(), 4)


def trim_walk(G0, mode, rng):
    G = nx.convert_node_labels_to_integers(G0)
    steps = 0
    while True:
        rem = removable(G)
        if not rem:
            return G, crit(G)
        scored = []
        for v in rem:
            H = G.copy(); H.remove_node(v)
            scored.append((crit(H), v))
        if mode == "preserve_zero":
            zeros = [v for c, v in scored if c == 0]
            pick = rng.choice(zeros) if zeros else rng.choice(
                [v for c, v in scored if c == min(c for c, _ in scored)])
        elif mode == "min_crit":
            mn = min(c for c, _ in scored)
            pick = rng.choice([v for c, v in scored if c == mn])
        else:
            pick = rng.choice(rem)
        G2 = G.copy(); G2.remove_node(pick)
        G = nx.convert_node_labels_to_integers(G2)
        steps += 1
        if steps > 60:
            return G, crit(G)


def run(G0, name, restarts=60):
    print(f"=== Trim {name}: n={G0.number_of_nodes()} m={G0.number_of_edges()} "
          f"crit={crit(G0)} removable={len(removable(G0))} ===", flush=True)
    best = None
    for mode in ("preserve_zero", "min_crit", "random"):
        for r in range(restarts):
            rng = random.Random(r * 7 + hash(mode) % 100)
            G, c = trim_walk(G0, mode, rng)
            if best is None or c < best[0]:
                best = (c, G.copy(), mode, r)
                print(f"  [{mode} r{r}] boundary n={G.number_of_nodes()} "
                      f"m={G.number_of_edges()} |E*|={c} vc={is_4vc(G)}", flush=True)
                if c == 0 and is_4vc(G) and dual_witness(G):
                    print(f"  *** DUAL-VERIFIED WITNESS from {name} ***", flush=True)
                    return best
    return best


if __name__ == "__main__":
    overall = None
    for n, k in [(6, 2), (8, 3)]:
        G = nx.convert_node_labels_to_integers(kneser(n, k))
        b = run(G, f"K({n},{k})", restarts=80 if (n, k) == (6, 2) else 25)
        if b and (overall is None or b[0] < overall[0]):
            overall = (b[0], b[1].copy(), f"K({n},{k})")
        if overall and overall[0] == 0 and dual_witness(overall[1]):
            break
    print(f"\nBEST: |E*|={overall[0]} from {overall[2]} "
          f"n={overall[1].number_of_nodes()} vc={is_4vc(overall[1])}", flush=True)
    if overall[0] == 0 and dual_witness(overall[1]):
        G2 = nx.convert_node_labels_to_integers(overall[1])
        with open("forge_kneser_WITNESS.txt", "w") as f:
            f.write(f"# WITNESS from {overall[2]}: n={G2.number_of_nodes()} m={G2.number_of_edges()}\n")
            for u, v in sorted(tuple(sorted(e)) for e in G2.edges()):
                f.write(f"{u} {v}\n")
        print("Saved forge_kneser_WITNESS.txt", flush=True)
