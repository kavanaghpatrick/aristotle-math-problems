#!/usr/bin/env python3
"""
forge_anneal.py — targeted search for an Erdos-944 witness via simulated annealing
over 4-vertex-critical graphs, minimizing the number of critical edges.

STATE: a 4-vertex-critical graph G (chi=4, every G-v 3-colorable).
ENERGY: number of critical edges (edges e with G-e 3-colorable). Witness = energy 0.

MOVES (each followed by a repair to restore vertex-criticality WITHOUT collapsing):
  1. add a random non-edge (creates more obstructions -> tends to make edges
     redundant, but may break vertex-criticality or push chi to 5).
  2. add a new vertex joined to 3-5 existing vertices.
  3. remove a non-critical vertex IF doing so keeps chi=4 (rare; shrinks graph).
  4. delete a redundant edge IF graph stays 4-vertex-critical (keeps it sparse).

REPAIR: after a move, if chi==5, reject. If chi==4 but some vertex non-critical,
we DO NOT strip (that collapses). Instead we reject the move (keep G). This keeps
the search on the manifold of 4-vertex-critical graphs.

Accept worse states with Metropolis probability exp(-dE/T), cooling schedule.

Seeds: best graphs from the exhaustive sweeps (n=9,10 champions) and random
4-vertex-critical graphs.
"""
import math
import random
import itertools
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, is_e944_witness)


def is_4vc(G):
    if is_k_colorable(G, 3):
        return False
    if not is_k_colorable(G, 4):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def critical_edge_count(G):
    c = 0
    for (u, v) in G.edges():
        H = G.copy(); H.remove_edge(u, v)
        if is_k_colorable(H, 3):
            c += 1
    return c


def random_move(G, rng, max_n=60):
    H = G.copy()
    nodes = list(H.nodes())
    r = rng.random()
    if r < 0.45:
        # add non-edge
        non = [(u, v) for u, v in itertools.combinations(nodes, 2)
               if not H.has_edge(u, v)]
        if not non:
            return None
        u, v = rng.choice(non)
        H.add_edge(u, v)
    elif r < 0.75 and H.number_of_nodes() < max_n:
        # add new vertex joined to k random vertices
        new = max([n for n in nodes if isinstance(n, int)], default=-1) + 1
        k = rng.randint(3, 5)
        for w in rng.sample(nodes, min(k, len(nodes))):
            H.add_edge(new, w)
    else:
        # delete a random edge
        if H.number_of_edges() == 0:
            return None
        e = rng.choice(list(H.edges()))
        H.remove_edge(*e)
    return H


def anneal(G0, iters=4000, T0=2.0, Tend=0.05, seed=0, max_n=60, log_prefix=""):
    rng = random.Random(seed)
    G = G0.copy()
    if not is_4vc(G):
        raise ValueError("seed not 4-vertex-critical")
    E = critical_edge_count(G)
    bestG, bestE = G.copy(), E
    for it in range(iters):
        T = T0 * (Tend / T0) ** (it / max(1, iters - 1))
        H = random_move(G, rng, max_n=max_n)
        if H is None or H.number_of_nodes() < 4:
            continue
        # must stay 4-vertex-critical (on-manifold)
        if not is_4vc(H):
            continue
        Eh = critical_edge_count(H)
        dE = Eh - E
        if dE <= 0 or rng.random() < math.exp(-dE / max(1e-6, T)):
            G, E = H, Eh
            if E < bestE:
                bestG, bestE = G.copy(), E
                print(f"{log_prefix}iter {it} T={T:.3f}: "
                      f"n={G.number_of_nodes()} m={G.number_of_edges()} "
                      f"critical_edges={E}")
                if E == 0:
                    print(f"{log_prefix}*** WITNESS: n={G.number_of_nodes()} "
                          f"m={G.number_of_edges()} ***")
                    return bestG, 0
    return bestG, bestE


def seed_from_g6(g6):
    return nx.from_graph6_bytes(g6.encode())


if __name__ == "__main__":
    import sys
    seeds = {
        "n9_champ": "HCp`fzy",
        "n10_champ": "ICpdbY{]_",
    }
    overall_best = None
    for name, g6 in seeds.items():
        G0 = seed_from_g6(g6)
        # relabel to ints
        G0 = nx.convert_node_labels_to_integers(G0)
        print(f"\n=== Annealing from {name} (g6={g6}) ===")
        print(f"  seed: n={G0.number_of_nodes()} m={G0.number_of_edges()} "
              f"critical_edges={critical_edge_count(G0)}")
        for trial in range(3):
            G, E = anneal(G0, iters=2500, seed=trial * 17 + 1,
                          max_n=55, log_prefix=f"  [{name} t{trial}] ")
            if overall_best is None or E < overall_best[1]:
                overall_best = (G.copy(), E, name, trial)
            if E == 0:
                break
        if overall_best and overall_best[1] == 0:
            break
    if overall_best:
        G, E, name, trial = overall_best
        print(f"\nOVERALL BEST: critical_edges={E} from {name} t{trial} "
              f"n={G.number_of_nodes()} m={G.number_of_edges()}")
        if E == 0:
            is_e944_witness(G)
            edges = sorted(tuple(sorted(e)) for e in G.edges())
            with open("forge_WITNESS.txt", "w") as f:
                f.write(f"# E944 WITNESS n={G.number_of_nodes()} m={G.number_of_edges()}\n")
                for u, v in edges:
                    f.write(f"{u} {v}\n")
            print("Saved witness to forge_WITNESS.txt")
        else:
            edges = sorted(tuple(sorted(e)) for e in G.edges())
            with open("forge_anneal_best.txt", "w") as f:
                f.write(f"# best anneal: n={G.number_of_nodes()} "
                        f"m={G.number_of_edges()} critical_edges={E}\n")
                for u, v in edges:
                    f.write(f"{u} {v}\n")
            print("Saved best to forge_anneal_best.txt")
