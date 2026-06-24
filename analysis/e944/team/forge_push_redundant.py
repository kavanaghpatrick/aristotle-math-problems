#!/usr/bin/env python3
"""
forge_push_redundant.py — push redundant-edge fraction toward 1.0.

We found 4-vertex-critical graphs with up to ~50% redundant edges in random
scans. Now: (1) capture the best candidates explicitly, (2) try to grow the
redundant fraction by larger/denser random scans and by a local-search /
simulated-annealing over edge additions that keeps the graph 4-vertex-critical
while reducing the number of critical edges.

GOAL: find G with chi=4, vertex-critical, ZERO critical edges.
"""
import itertools
import random
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, summary, is_e944_witness)
from forge_redundant_probe import make_vertex_critical_4, count_redundant


def edgelist_str(G):
    return sorted(tuple(sorted(e)) for e in G.edges())


def best_random(n, p, trials, seed=1, target_zero=True):
    """Return the 4-vertex-critical graph minimizing #critical edges."""
    best = None  # (num_critical, G)
    for t in range(trials):
        G = nx.gnp_random_graph(n, p, seed=seed + t)
        if chromatic_number(G) != 4:
            continue
        H = make_vertex_critical_4(G)
        if H is None or H.number_of_nodes() < 4:
            continue
        vc, chi, bad = is_vertex_critical(H)
        if not vc or chi != 4:
            continue
        ce = critical_edges(H, 4)
        nc = len(ce)
        if best is None or nc < best[0]:
            best = (nc, H.copy())
            print(f"  n={H.number_of_nodes()} m={H.number_of_edges()} "
                  f"critical_edges={nc} redundant={H.number_of_edges()-nc}")
            if nc == 0:
                print("  *** ZERO CRITICAL EDGES — WITNESS CANDIDATE ***")
                return best
    return best


def local_search_reduce_critical(G0, iters=2000, seed=0):
    """
    Local search: start from a 4-vertex-critical G0. Repeatedly try adding a
    random non-edge. If the result is still 4-chromatic and we can reduce to a
    4-vertex-critical graph with FEWER critical edges, accept.
    Adding edges destroys criticality of edges (more obstructions), but may also
    break vertex-criticality; we re-reduce after each move.
    """
    random.seed(seed)
    G = G0.copy()
    best_nc = len(critical_edges(G, 4))
    n_nodes = G.number_of_nodes()
    nodes = list(G.nodes())
    history = [best_nc]
    for it in range(iters):
        # candidate move: add an edge, OR add a new vertex connected to a random
        # subset (to grow the graph), then re-reduce to vertex-critical.
        H = G.copy()
        move = random.random()
        if move < 0.5 and n_nodes < 40:
            # add a new vertex joined to a random subset of size 3..5
            new = ("x", it)
            k = random.randint(3, 5)
            tgt = random.sample(list(H.nodes()), min(k, H.number_of_nodes()))
            for w in tgt:
                H.add_edge(new, w)
        else:
            non_edges = [(u, v) for u, v in itertools.combinations(H.nodes(), 2)
                         if not H.has_edge(u, v)]
            if not non_edges:
                continue
            u, v = random.choice(non_edges)
            H.add_edge(u, v)
        if chromatic_number(H) != 4:
            continue
        Hc = make_vertex_critical_4(H)
        if Hc is None:
            continue
        vc, chi, bad = is_vertex_critical(Hc)
        if not vc or chi != 4:
            continue
        nc = len(critical_edges(Hc, 4))
        # accept if strictly better, or equal with small prob (plateau move)
        if nc < best_nc or (nc == best_nc and random.random() < 0.3):
            G = Hc
            n_nodes = G.number_of_nodes()
            if nc < best_nc:
                best_nc = nc
                history.append(nc)
                print(f"  iter {it}: n={G.number_of_nodes()} "
                      f"m={G.number_of_edges()} critical_edges={nc}")
                if nc == 0:
                    print("  *** ZERO CRITICAL EDGES ***")
                    return G, 0
    return G, best_nc


if __name__ == "__main__":
    print("=== Step 1: best random 4-vertex-critical (min critical edges) ===")
    overall = None
    for (n, p) in [(11, 0.42), (12, 0.40), (13, 0.38), (14, 0.36),
                   (15, 0.35), (16, 0.34), (18, 0.32)]:
        print(f"\n-- G({n},{p}), 400 trials --")
        b = best_random(n, p, 400, seed=7)
        if b and (overall is None or b[0] < overall[0]):
            overall = b
    if overall:
        print(f"\nBest random: critical_edges={overall[0]} "
              f"n={overall[1].number_of_nodes()} m={overall[1].number_of_edges()}")
        print("Edges:", edgelist_str(overall[1]))
        print("\n=== Step 2: local search from best random ===")
        G, nc = local_search_reduce_critical(overall[1], iters=1500, seed=3)
        print(f"\nAfter local search: critical_edges={nc} "
              f"n={G.number_of_nodes()} m={G.number_of_edges()}")
        if nc == 0:
            is_e944_witness(G)
            print("Edges:", edgelist_str(G))
