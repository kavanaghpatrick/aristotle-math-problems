"""
INVENTION BLITZ — jensen lane, ROUND 4. Per skeptic: pivot to ASYMMETRIC DENSITY
(not transitive substrates). Push the J6 lead (asymmetric chords on a vertex-critical
seed reduced critical edges 26→13, preserving vertex-criticality).

STRATEGY: greedy/beam asymmetric densification. Start from a vertex-critical χ=4 seed
(small circulant). Repeatedly ADD the single chord that most reduces #critical-edges
WHILE preserving (χ=4 ∧ vertex-critical). Track whether #critical drops below the
13-floor and whether δ rises toward 6. Asymmetric because we add individual chords
(breaking transitivity), exactly skeptic's recommended regime.

Also J9: same but allowing edge SWAPS (add one, remove one) to keep moving when pure
addition stalls — a local search on the (χ=4 ∧ vertex-critical) manifold minimizing
#critical, staying asymmetric.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools, random
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def ncrit(G):
    return len(critical_edges(G))


def vc4(G):
    return chromatic_number(G) == 4 and is_vertex_critical(G, 4)


def greedy_densify(G0, max_steps=40, verbose=False):
    """Add chords that reduce #critical-edges while preserving χ=4 ∧ vertex-critical."""
    G = G0.copy()
    assert vc4(G), "seed must be χ=4 vertex-critical"
    cur = ncrit(G)
    n = G.number_of_nodes()
    history = [cur]
    for step in range(max_steps):
        nonedges = [(i, j) for i in range(n) for j in range(i+1, n) if not G.has_edge(i, j)]
        best = None  # (new_ncrit, edge)
        for (i, j) in nonedges:
            G.add_edge(i, j)
            if chromatic_number(G) == 4 and is_vertex_critical(G, 4):
                c = ncrit(G)
                if best is None or c < best[0]:
                    best = (c, (i, j))
            G.remove_edge(i, j)
        if best is None or best[0] >= cur:
            break  # no improving chord
        G.add_edge(*best[1]); cur = best[0]; history.append(cur)
        if verbose:
            print(f"  step {step+1}: +{best[1]} → #critical={cur}, δ={min(d for _,d in G.degree())}", flush=True)
        if cur == 0:
            break
    return G, cur, history


if __name__ == "__main__":
    print("=== BLITZ ROUND 4 (jensen) — asymmetric greedy densification ===")
    seeds = [
        ("C13(1,5)", nx.circulant_graph(13, [1, 5])),
        ("C13(2,3)", nx.circulant_graph(13, [2, 3])),
        ("C13(1,2,5)", nx.circulant_graph(13, [1, 2, 5])),
        ("C16(1,2,5)", nx.circulant_graph(16, [1, 2, 5])),
    ]
    overall_best = None
    for name, G0 in seeds:
        if not vc4(G0):
            print(f"{name}: seed not χ=4 vertex-critical (χ={chromatic_number(G0)}), skip")
            continue
        c0 = ncrit(G0)
        print(f"\n{name}: seed n={G0.number_of_nodes()} m={G0.number_of_edges()} δ={min(d for _,d in G0.degree())} #critical={c0}", flush=True)
        G, cur, hist = greedy_densify(G0, max_steps=30, verbose=True)
        dmin = min(d for _, d in G.degree())
        print(f"  → final n={G.number_of_nodes()} m={G.number_of_edges()} δ={dmin} #critical={cur} (from {c0}); trajectory {hist}", flush=True)
        if overall_best is None or cur < overall_best[0]:
            overall_best = (cur, name, G.number_of_nodes(), dmin)
    print(f"\nOVERALL BEST: #critical={overall_best[0]} at {overall_best[1]} (n={overall_best[2]}, δ={overall_best[3]})")
    print("(13-floor = the 5-method-convergent minimum; below 13 with vertex-crit = real progress; 0 = witness)")
