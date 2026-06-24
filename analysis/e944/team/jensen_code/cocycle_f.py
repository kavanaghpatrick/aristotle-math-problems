"""
wall's cocycle invariant f(G) = min over proper-or-not 3-colorings of #monochromatic edges.
witness ⟺ f(G) ≥ 2 ∧ vertex-critical; impossibility = "vertex-critical ⟹ f ≤ 1".

Connection to my work + gallai's B₁:
  f(G)=0 ⟺ G is 3-colorable.
  f(G)=1 ⟺ ∃ a 3-coloring with exactly ONE monochromatic edge uv ⟺ G−uv is 3-colorable
           ⟺ uv is a CRITICAL edge (and that coloring witnesses it). So for χ=4 G:
           f(G)=1 ⟺ E*(G) ≠ ∅ (gallai's B₁>0).
  f(G)≥2 ⟺ every 3-coloring has ≥2 monochromatic edges ⟺ NO single edge is critical via a
           1-bad-edge coloring ⟺ (with χ=4) E*=∅ on the "reachable by 1-bad coloring" edges.

Construction-side target (wall): show modular J–S graphs have f=1 (E* spanning ⟹ some edge is the
single bad edge of a coloring), and parallelization keeps f=1 — direct evidence witness ⊄ modular.

We compute f(G) exactly for small graphs by minimizing #monochromatic edges over all 3-colorings
(via ILP-free exhaustive/backtracking for small n, or a min over sampled+greedy for larger).
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def f_invariant_exact(G, cap=None):
    """Exact min #monochromatic edges over ALL 3-colorings, via backtracking with
    branch-and-bound on the running mono-edge count. cap: optional early stop if
    we just need to know whether f<=cap (returns min(f,cap+1))."""
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    adj = [[] for _ in range(n)]
    for u, v in G.edges():
        adj[idx[u]].append(idx[v]); adj[idx[v]].append(idx[u])
    order = sorted(range(n), key=lambda i: len(adj[i]), reverse=True)
    pos = {v: p for p, v in enumerate(order)}
    # adjacency restricted to earlier-in-order neighbors
    earlier = [[] for _ in range(n)]
    for i in range(n):
        for j in adj[i]:
            if pos[j] < pos[i]:
                earlier[i].append(j)
    best = [G.number_of_edges() + 1]
    color = [0] * n

    def bt(p, mono):
        if mono >= best[0]:
            return
        if cap is not None and mono > cap:
            return
        if p == n:
            best[0] = mono
            return
        v = order[p]
        for c in range(3):
            extra = sum(1 for j in earlier[v] if color[j] == c)
            if mono + extra < best[0]:
                color[v] = c
                bt(p + 1, mono + extra)
    bt(0, 0)
    return best[0]


def report_f(G, name):
    chi = chromatic_number(G)
    f = f_invariant_exact(G)
    line = f"{name}: n={G.number_of_nodes()} χ={chi} f(G)={f}"
    if chi == 4:
        ce = critical_edges(G)
        line += f" |E*|={len(ce)}"
        # check the connection: f=1 ⟺ |E*|>0
        line += f"  [f=1⟺E*≠∅: {(f==1)==(len(ce)>0)}]"
    print(line, flush=True)
    return f


if __name__ == "__main__":
    print("=== wall's cocycle f(G) on known graphs (validate f=1 ⟺ E*≠∅) ===")
    report_f(nx.complete_graph(4), "K4")                 # χ=4, E*≠∅ ⟹ f=1
    report_f(nx.cycle_graph(5), "C5")                    # χ=3 ⟹ f=0
    report_f(nx.circulant_graph(13, [1, 2, 5]), "C13(1,2,5)")  # χ=4 vertex-crit, E*≠∅ ⟹ f=1
    print()
    print("=== f(G) on my J–S constructions (construction-side: modular ⟹ f=1) ===")
    sys.path.insert(0, os.path.dirname(__file__))
    from jensen_siggers import build_Hprime, four_critical_subgraph
    for m in (2,):
        Hp, SG, B2, Gg = build_Hprime(m)
        H = four_critical_subgraph(Hp)
        report_f(H, f"J–S H(m={m}) [single modular gadget]")
