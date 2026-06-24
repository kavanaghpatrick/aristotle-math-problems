#!/usr/bin/env python3
"""
forge_reverse_repair.py — forge-9: the UNTRIED DIRECTION.

Every prior method APPROACHED a witness from "make vertex-critical, then kill
critical edges" (trimming) — which always collapses redundancy. This goes the
OTHER way: START from a graph with 0 critical edges (easy to get — Kneser K(6,2),
voltage covers, blow-ups all reach |E*|=0) that is NOT vertex-critical, then
REPAIR vertex-criticality by adding minimal structure to criticalize each
removable vertex WITHOUT creating a critical edge.

Seed sources for 0-critical-edge δ≥6 graphs: K(6,2) (6-regular, |E*|=0), K(8,3).
Repair move: for a removable vertex v (χ(G−v)=4), we must DROP χ(G−v) to 3. The
minimal way: add edges among N(v)'s non-neighbors or contract structure so that
G−v becomes 3-colorable — but adding edges elsewhere may create critical edges.
We search: for each removable v, find an edge addition (or small gadget) that
makes v critical and check it doesn't create a critical edge; accept greedily.

Honest expectation: making v critical means G−v drops to χ=3, i.e. v was
"holding up" a 4-obstruction — but in a 0-critical-edge graph the obstruction is
edge-robust, so removing v shouldn't drop χ... this is exactly the robustness-
asymmetry. The test: can ANY local repair criticalize a vertex without breaking
edge-redundancy? If not on K(6,2)/K(8,3), it's the Nth confirmation; if yes, lead.
"""
import itertools
import random
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def kneser(n, k):
    V = list(itertools.combinations(range(n), k))
    G = nx.Graph(); G.add_nodes_from(V)
    for a, b in itertools.combinations(V, 2):
        if not (set(a) & set(b)):
            G.add_edge(a, b)
    return nx.convert_node_labels_to_integers(G)


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


def repair_round(G, rng):
    """One repair pass: try to criticalize a removable vertex without creating a
    critical edge. Moves tried: add an edge between two non-adjacent vertices
    (anywhere), or add a new vertex joined to a subset, choosing moves that REDUCE
    #removable without increasing |E*|."""
    rem = removable(G)
    if not rem:
        return G, True  # already vertex-critical
    base_rem = len(rem)
    base_crit = crit(G)
    nodes = list(G.nodes())
    cands = []
    # candidate moves: add a non-edge
    non_edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if not G.has_edge(u, v)]
    rng.shuffle(non_edges)
    for (u, v) in non_edges[:200]:
        H = G.copy(); H.add_edge(u, v)
        if not chi4(H):
            continue
        nr = len(removable(H))
        nc = crit(H)
        if nr < base_rem and nc <= base_crit:
            cands.append((nr, nc, ("addedge", u, v)))
    if not cands:
        return G, False
    cands.sort()
    nr, nc, mv = cands[0]
    H = G.copy(); H.add_edge(mv[1], mv[2])
    return nx.convert_node_labels_to_integers(H), None


def repair(G0, max_rounds=30, seed=0, log=""):
    rng = random.Random(seed)
    G = nx.convert_node_labels_to_integers(G0)
    print(f"{log} start: n={G.number_of_nodes()} m={G.number_of_edges()} "
          f"|E*|={crit(G)} removable={len(removable(G))}", flush=True)
    for rd in range(max_rounds):
        if is_4vc(G):
            c = crit(G)
            print(f"{log} VERTEX-CRITICAL reached round {rd}: |E*|={c}", flush=True)
            return G, c
        G2, done = repair_round(G, rng)
        if done is False:
            print(f"{log} STUCK round {rd}: removable={len(removable(G))} "
                  f"|E*|={crit(G)} (no repair move reduces removable w/o adding critical edge)",
                  flush=True)
            return G, crit(G)
        G = G2
        if rd % 3 == 0:
            print(f"{log} round {rd}: n={G.number_of_nodes()} m={G.number_of_edges()} "
                  f"removable={len(removable(G))} |E*|={crit(G)}", flush=True)
    return G, crit(G)


if __name__ == "__main__":
    seeds = [("K(6,2)", kneser(6, 2)), ("K(8,3)", kneser(8, 3))]
    best = None
    for name, G0 in seeds:
        print(f"\n=== Reverse-repair from {name} (|E*|={crit(G0)}, NOT vertex-critical) ===", flush=True)
        for t in range(4):
            G, c = repair(G0, max_rounds=25, seed=t * 19 + 1, log=f"[{name} t{t}]")
            if is_4vc(G):
                if c == 0 and dual_witness(G):
                    print(f"  *** DUAL-VERIFIED WITNESS from {name} ***", flush=True)
                    best = (0, G.copy(), name)
                    break
                if best is None or c < best[0]:
                    best = (c, G.copy(), name)
        if best and best[0] == 0:
            break
    if best:
        print(f"\nBEST reverse-repair: |E*|={best[0]} from {best[2]} "
              f"n={best[1].number_of_nodes()} vc={is_4vc(best[1])}", flush=True)
