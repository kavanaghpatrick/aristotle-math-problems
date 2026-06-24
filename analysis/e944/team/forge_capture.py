#!/usr/bin/env python3
"""
forge_capture.py — capture the high-redundancy 4-vertex-critical graphs found
in the random scan, store their exact edge lists, and analyze structure.

The earlier scan (forge_redundant_probe, seed=1) found e.g.
  G(16,0.35) trial 53: n=10 m=21 redundant=11 critical=10.
We reproduce EXACTLY by re-running the same seed path and capturing the graph,
then study it: which edges are redundant, what obstructions survive, is it close
to a witness?
"""
import random
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, summary, is_e944_witness)
from forge_redundant_probe import make_vertex_critical_4, count_redundant


def reproduce(n, p, seed_base, trial):
    G = nx.gnp_random_graph(n, p, seed=seed_base + trial)
    if chromatic_number(G) != 4:
        return None
    H = make_vertex_critical_4(G)
    return H


def analyze(H, name=""):
    chi = chromatic_number(H)
    vc, _, bad = is_vertex_critical(H)
    ce = critical_edges(H, chi)
    m = H.number_of_edges()
    print(f"[{name}] n={H.number_of_nodes()} m={m} chi={chi} "
          f"vertex_critical={vc} critical_edges={len(ce)} "
          f"redundant={m-len(ce)}  ({100*(m-len(ce))//m if m else 0}% redundant)")
    print(f"  degree seq: {sorted([d for _,d in H.degree()], reverse=True)}")
    print(f"  critical edges: {sorted(tuple(sorted(e)) for e in ce)}")
    return H, ce


if __name__ == "__main__":
    # Reproduce the best finds from forge_redundant_probe (seed=1).
    print("=== Reproducing high-redundancy finds ===")
    candidates = []
    for (n, p, trial) in [(16, 0.35, 53), (10, 0.45, 112), (14, 0.38, 60),
                          (20, 0.32, 76)]:
        H = reproduce(n, p, 1, trial)
        if H is not None and chromatic_number(H) == 4:
            vc, _, _ = is_vertex_critical(H)
            if vc:
                nm = f"G({n},{p})#{trial}"
                analyze(H, nm)
                candidates.append((nm, H))
                print()

    # Save the densest-redundancy candidate to a file for the squad.
    if candidates:
        best = min(candidates,
                   key=lambda x: len(critical_edges(x[1], 4)))
        nm, H = best
        edges = sorted(tuple(sorted(e)) for e in H.edges())
        with open("forge_best_candidate.txt", "w") as f:
            f.write(f"# Best high-redundancy 4-vertex-critical candidate: {nm}\n")
            f.write(f"# n={H.number_of_nodes()} m={H.number_of_edges()} "
                    f"critical_edges={len(critical_edges(H,4))}\n")
            for u, v in edges:
                f.write(f"{u} {v}\n")
        print(f"Saved best candidate {nm} to forge_best_candidate.txt")
