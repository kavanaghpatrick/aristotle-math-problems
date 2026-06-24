#!/usr/bin/env python3
"""
critedge.py — exact chromatic number, vertex-criticality, and critical-EDGE
analysis for the E944 squad (count).

Definitions match the LOCKED Lean defs in
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean:

  chromaticNumber(G)         = least k with a proper k-coloring (exact).
  IsCritical G k             = chi(G)==k AND for every vertex v, chi(G - v) < chi(G).
                               (VERTEX-critical: every vertex deletion drops chi.)
  IsCriticalEdges G S        = chi(G - S) < chi(G)   (S a set of edges)
  IsCriticalEdge  G e        = chi(G - e) < chi(G)
  IsErdos944 G 4 1           = IsCritical G 4 AND no single edge is critical.

We compute chi EXACTLY by a DSATUR-seeded branch-and-bound / direct k-colorability
test. Correctness over the small graphs we care about (n <= ~16) is verified by
cross-checking against an independent ILP-free k-colorability search and against
known chromatic numbers of named graphs in the self-test.
"""
import itertools
import networkx as nx
from functools import lru_cache


# ---------------------------------------------------------------------------
# Exact k-colorability test (backtracking with DSATUR ordering + clique LB).
# ---------------------------------------------------------------------------
def is_k_colorable(G, k):
    """True iff G has a proper coloring with <= k colors. Exact."""
    n = G.number_of_nodes()
    if k <= 0:
        return n == 0
    if n == 0:
        return True
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [set() for _ in range(n)]
    for u, v in G.edges():
        if u == v:
            continue
        adj[idx[u]].add(idx[v])
        adj[idx[v]].add(idx[u])

    color = [-1] * n
    # DSATUR-style dynamic ordering: pick uncolored vertex with max saturation,
    # tie-break by degree.
    deg = [len(adj[i]) for i in range(n)]

    def saturation(i):
        return len({color[j] for j in adj[i] if color[j] != -1})

    def backtrack(num_colored):
        if num_colored == n:
            return True
        # choose next vertex
        best = -1
        best_key = None
        for i in range(n):
            if color[i] == -1:
                key = (saturation(i), deg[i])
                if best_key is None or key > best_key:
                    best_key = key
                    best = i
        i = best
        used = {color[j] for j in adj[i] if color[j] != -1}
        # symmetry breaking: only try colors up to (max used so far)+1
        max_used = max([color[j] for j in range(n) if color[j] != -1], default=-1)
        limit = min(k, max_used + 2)
        for c in range(limit):
            if c in used:
                continue
            color[i] = c
            if backtrack(num_colored + 1):
                return True
            color[i] = -1
        return False

    return backtrack(0)


def chromatic_number(G):
    """Exact chromatic number. Handles isolated vertices and empty graph."""
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if G.number_of_edges() == 0:
        return 1
    # lower bound: largest clique we can find quickly; upper bound: n
    lb = 1
    try:
        lb = max(len(c) for c in nx.find_cliques(G))
    except Exception:
        lb = 2
    for k in range(lb, n + 1):
        if is_k_colorable(G, k):
            return k
    return n


# ---------------------------------------------------------------------------
# Criticality predicates
# ---------------------------------------------------------------------------
def is_vertex_critical(G, k=None):
    """IsCritical G k: chi(G)==k and deleting ANY vertex strictly drops chi."""
    chi = chromatic_number(G)
    if k is not None and chi != k:
        return False
    if G.number_of_nodes() == 0:
        return False
    for v in list(G.nodes()):
        H = G.copy()
        H.remove_node(v)
        if chromatic_number(H) >= chi:
            return False
    return True


def critical_edges(G):
    """Return the list of single edges e such that chi(G - e) < chi(G)."""
    chi = chromatic_number(G)
    out = []
    for u, v in G.edges():
        H = G.copy()
        H.remove_edge(u, v)
        if chromatic_number(H) < chi:
            out.append((u, v))
    return out


def num_critical_edges(G):
    return len(critical_edges(G))


def is_edge_critical(G, k=None):
    """Standard k-edge-critical: chi==k and EVERY edge is critical."""
    chi = chromatic_number(G)
    if k is not None and chi != k:
        return False
    return num_critical_edges(G) == G.number_of_edges()


def is_erdos944_witness(G, k=4):
    """IsErdos944 G k 1: k-vertex-critical AND no single critical edge."""
    if not is_vertex_critical(G, k):
        return False
    return num_critical_edges(G) == 0


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------
def _selftest():
    ok = True

    def check(name, got, want):
        nonlocal ok
        status = "OK " if got == want else "FAIL"
        if got != want:
            ok = False
        print(f"  [{status}] {name}: got {got}, want {want}")

    # Chromatic numbers of named graphs
    check("chi(K4)", chromatic_number(nx.complete_graph(4)), 4)
    check("chi(C5)", chromatic_number(nx.cycle_graph(5)), 3)
    check("chi(C6)", chromatic_number(nx.cycle_graph(6)), 2)
    check("chi(Petersen)", chromatic_number(nx.petersen_graph()), 3)
    check("chi(K33)", chromatic_number(nx.complete_bipartite_graph(3, 3)), 2)
    check("chi(Grotzsch=11v triangle-free chi4)",
          chromatic_number(nx.mycielskian(nx.cycle_graph(5))), 4)
    check("chi(empty3)", chromatic_number(nx.empty_graph(3)), 1)

    # K4 is 4-vertex-critical AND 4-edge-critical; every edge critical
    K4 = nx.complete_graph(4)
    check("K4 vertex-critical(4)", is_vertex_critical(K4, 4), True)
    check("K4 #critical-edges == 6", num_critical_edges(K4), 6)
    check("K4 is_erdos944_witness", is_erdos944_witness(K4, 4), False)

    # C5 is 3-vertex-critical and 3-edge-critical (odd cycle): every edge critical
    C5 = nx.cycle_graph(5)
    check("C5 vertex-critical(3)", is_vertex_critical(C5, 3), True)
    check("C5 #critical-edges == 5", num_critical_edges(C5), 5)

    # Cross-check is_k_colorable vs brute force on a few random small graphs
    import random
    rng = random.Random(12345)
    for t in range(40):
        n = rng.randint(3, 7)
        p = rng.random()
        Gr = nx.gnp_random_graph(n, p, seed=rng.randint(0, 10**6))
        chi = chromatic_number(Gr)
        # brute-force chi via direct assignment search
        bf = _brute_chi(Gr)
        if chi != bf:
            ok = False
            print(f"  [FAIL] random graph chi mismatch: dsatur={chi} brute={bf} "
                  f"edges={sorted(Gr.edges())}")
    print("  [OK ] 40 random graphs cross-checked dsatur-chi vs brute-chi"
          if ok else "  [FAIL] random cross-check")

    print("SELFTEST", "PASSED" if ok else "FAILED")
    return ok


def _brute_chi(G):
    """Independent exact chi via exhaustive color-assignment search (small n)."""
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if G.number_of_edges() == 0:
        return 1
    nodes = list(G.nodes())
    for k in range(1, n + 1):
        # try all colorings with k colors (with first vertex fixed to 0 for symmetry)
        def rec(i, assign):
            if i == n:
                return True
            v = nodes[i]
            for c in range(k):
                if all(assign.get(u, -1) != c for u in G.neighbors(v)):
                    assign[v] = c
                    if rec(i + 1, assign):
                        return True
                    del assign[v]
            return False
        if rec(0, {}):
            return k
    return n


if __name__ == "__main__":
    _selftest()
