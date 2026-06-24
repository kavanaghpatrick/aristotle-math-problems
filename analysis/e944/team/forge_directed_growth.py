#!/usr/bin/env python3
"""
forge_directed_growth.py — directed growth toward an Erdos-944 witness.

Lesson from annealing: random moves almost always break vertex-criticality, so
the 4-vertex-critical manifold is rigid. Lesson from circulants: symmetry forces
one load-bearing orbit. Lesson from overlay: need enough vertices for parallel
obstructions; union of two 4-critical graphs isn't vertex-critical.

NEW APPROACH — eliminate critical edges one at a time by adding a NEW vertex
that creates a SECOND obstruction through the critical edge, while staying
vertex-critical.

For a critical edge e=(a,b): in some 3-coloring of G-e, a and b get the SAME
color (that's why adding e back forces 4 colors / why removing e allows 3
colors). To make e redundant we must ensure G-e is STILL 4-chromatic, i.e. add
structure forcing 4 colors even without e. We attach a gadget that forces a,b to
differ (an "indicator" path of even length plus a triangle) WITHOUT using edge e,
so the 4-chromaticity survives e's removal.

Practically we try, for each critical edge e and each small gadget attachment,
the move "add gadget" and test if (i) still 4-vertex-critical and (ii) e becomes
redundant and (iii) net critical-edge count drops. Greedy + backtracking.

This is exact and verification-driven; we accept only moves that VERIFY a drop.
"""
import itertools
import random
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


def crit_edges(G):
    out = []
    for (u, v) in G.edges():
        H = G.copy(); H.remove_edge(u, v)
        if is_k_colorable(H, 3):
            out.append((u, v))
    return out


def fresh(G):
    return max([v for v in G.nodes() if isinstance(v, int)], default=-1) + 1


def try_gadgets_for_edge(G, e, rng, max_attach=6, samples=120):
    """
    Try adding a small gadget anchored near edge e to make e redundant while
    keeping G 4-vertex-critical and not increasing total critical edges.
    Gadget templates:
      T1: one new vertex z joined to a random k in {3,4} existing vertices
          INCLUDING both endpoints of e (forces local density around e).
      T2: two new vertices z1,z2 forming a triangle with one endpoint, plus
          edges to a few others (a K4-minus-edge ear).
    Returns improved G or None.
    """
    a, b = e
    base_nc = len(crit_edges(G))
    nodes = list(G.nodes())
    best = None
    for _ in range(samples):
        H = G.copy()
        t = rng.random()
        if t < 0.5:
            z = fresh(H)
            others = [v for v in nodes if v not in (a, b)]
            k = rng.randint(1, 3)
            attach = [a, b] + rng.sample(others, min(k, len(others)))
            for w in attach:
                H.add_edge(z, w)
        else:
            z1, z2 = fresh(H), fresh(H) + 1
            H.add_edge(z1, z2)
            H.add_edge(z1, a)
            H.add_edge(z2, b)
            others = [v for v in nodes if v not in (a, b)]
            k = rng.randint(1, 3)
            for w in rng.sample(others, min(k, len(others))):
                H.add_edge(rng.choice([z1, z2]), w)
        if H.number_of_nodes() > 70:
            continue
        if not is_4vc(H):
            continue
        nc = len(crit_edges(H))
        if nc < base_nc:
            if best is None or nc < best[0]:
                best = (nc, H.copy())
    return best


def grow(G0, max_rounds=40, seed=0, log_prefix=""):
    rng = random.Random(seed)
    G = G0.copy()
    if not is_4vc(G):
        raise ValueError("seed not 4vc")
    nc = len(crit_edges(G))
    print(f"{log_prefix}start: n={G.number_of_nodes()} m={G.number_of_edges()} "
          f"critical_edges={nc}", flush=True)
    for rd in range(max_rounds):
        ce = crit_edges(G)
        if not ce:
            print(f"{log_prefix}*** WITNESS at round {rd} ***", flush=True)
            return G, 0
        # try to eliminate the critical edge that is 'easiest' (try each, take best)
        improved = None
        rng.shuffle(ce)
        for e in ce[:8]:
            cand = try_gadgets_for_edge(G, e, rng)
            if cand is not None:
                if improved is None or cand[0] < improved[0]:
                    improved = cand
        if improved is None:
            print(f"{log_prefix}stuck at round {rd}: n={G.number_of_nodes()} "
                  f"critical_edges={len(ce)} (no gadget reduced count)", flush=True)
            return G, len(ce)
        G = improved[1]
        nc = improved[0]
        print(f"{log_prefix}round {rd}: n={G.number_of_nodes()} "
              f"m={G.number_of_edges()} critical_edges={nc}", flush=True)
    return G, len(crit_edges(G))


if __name__ == "__main__":
    seeds = {"n10_champ": "ICpdbY{]_", "n9_champ": "HCp`fzy"}
    best = None
    for name, g6 in seeds.items():
        G0 = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
        for trial in range(4):
            print(f"\n=== Directed growth from {name} trial {trial} ===", flush=True)
            G, nc = grow(G0, max_rounds=50, seed=trial * 101 + 7,
                         log_prefix=f"[{name} t{trial}] ")
            if best is None or nc < best[1]:
                best = (G.copy(), nc, name, trial)
            if nc == 0:
                break
        if best and best[1] == 0:
            break
    G, nc, name, trial = best
    print(f"\nBEST: critical_edges={nc} n={G.number_of_nodes()} "
          f"m={G.number_of_edges()} from {name} t{trial}", flush=True)
    if nc == 0:
        is_e944_witness(G)
        with open("forge_WITNESS.txt", "w") as f:
            f.write(f"# E944 WITNESS n={G.number_of_nodes()} m={G.number_of_edges()}\n")
            for u, v in sorted(tuple(sorted(e)) for e in G.edges()):
                f.write(f"{u} {v}\n")
        print("Saved forge_WITNESS.txt", flush=True)
    else:
        with open("forge_growth_best.txt", "w") as f:
            f.write(f"# best directed growth n={G.number_of_nodes()} "
                    f"m={G.number_of_edges()} critical_edges={nc}\n")
            for u, v in sorted(tuple(sorted(e)) for e in G.edges()):
                f.write(f"{u} {v}\n")
        print("Saved forge_growth_best.txt", flush=True)
