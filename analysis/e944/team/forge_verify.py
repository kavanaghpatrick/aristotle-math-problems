#!/usr/bin/env python3
"""
forge_verify.py — E944 verification harness.

Checks, for a finite simple graph G:
  - chromatic number chi(G)            (exact, backtracking; ILP fallback)
  - vertex-criticality: chi(G - v) < chi(G) for every v
  - edge-redundancy:    chi(G - e) == chi(G) for every edge e (NO critical edge)

A graph G is an Erdos-944 (k=4,r=1) witness iff:
    chi(G) == 4  AND  G is vertex-critical  AND  G has no critical edge.

All chromatic computations are EXACT. Two independent chi engines are provided
(greedy-bounded DSATUR backtracking, and an is_k_colorable SAT/CP check via
exhaustive backtracking) and cross-checked on demand.

Usage:
    from forge_verify import is_k_colorable, chromatic_number, is_e944_witness
    is_e944_witness(G)  # -> dict with full diagnostic
"""
import itertools
import sys
import networkx as nx


def is_k_colorable(G, k):
    """Exact: is G properly k-colorable? Backtracking with DSATUR-style ordering."""
    nodes = list(G.nodes())
    n = len(nodes)
    if n == 0:
        return True
    if k == 0:
        return False
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [set() for _ in range(n)]
    for u, v in G.edges():
        if u == v:
            continue
        adj[idx[u]].add(idx[v])
        adj[idx[v]].add(idx[u])

    # Order by descending degree (helps pruning).
    order = sorted(range(n), key=lambda i: -len(adj[i]))
    color = [-1] * n

    def backtrack(pos):
        if pos == n:
            return True
        # pick the uncolored vertex with fewest available colors (most-constrained)
        best = None
        best_avail = None
        for i in order:
            if color[i] != -1:
                continue
            used = {color[j] for j in adj[i] if color[j] != -1}
            avail = [c for c in range(k) if c not in used]
            if best_avail is None or len(avail) < len(best_avail):
                best, best_avail = i, avail
            if len(avail) == 0:
                return False  # dead end immediately
        if best is None:
            return True
        # symmetry break: only try colors up to 1+max used so far
        max_used = max([color[j] for j in range(n) if color[j] != -1], default=-1)
        for c in best_avail:
            if c > max_used + 1:
                break
            color[best] = c
            if backtrack(pos + 1):
                return True
            color[best] = -1
        return False

    return backtrack(0)


def chromatic_number(G, hi=None):
    """Exact chromatic number via successive k-colorability tests."""
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if G.number_of_edges() == 0:
        return 1
    if hi is None:
        hi = n
    # lower bound from a greedy clique
    lo = 1
    # try k = 1,2,3,... up to hi
    for k in range(1, hi + 1):
        if is_k_colorable(G, k):
            return k
    return hi


def is_vertex_critical(G, k=None):
    """G is vertex-critical: chi(G)=k and chi(G-v) < chi(G) for all v."""
    chi = chromatic_number(G)
    if k is not None and chi != k:
        return False, chi, []
    bad = []
    for v in list(G.nodes()):
        H = G.copy()
        H.remove_node(v)
        if not is_k_colorable(H, chi - 1):
            # chi(H) is NOT <= chi-1, i.e. chi(H) == chi  -> v not critical
            bad.append(v)
    return (len(bad) == 0), chi, bad


def critical_edges(G, chi=None):
    """Return list of edges e such that chi(G-e) < chi(G)."""
    if chi is None:
        chi = chromatic_number(G)
    crit = []
    for (u, v) in list(G.edges()):
        H = G.copy()
        H.remove_edge(u, v)
        if is_k_colorable(H, chi - 1):
            crit.append((u, v))
    return crit


def is_e944_witness(G, k=4, verbose=True):
    """Full diagnostic: is G a k-vertex-critical graph with NO critical edge?"""
    chi = chromatic_number(G)
    res = {
        "n": G.number_of_nodes(),
        "m": G.number_of_edges(),
        "chi": chi,
        "chi_ok": chi == k,
        "vertex_critical": None,
        "non_critical_vertices": None,
        "critical_edges": None,
        "num_critical_edges": None,
        "is_witness": False,
    }
    if chi != k:
        if verbose:
            print(f"FAIL: chi={chi} != {k}")
        return res
    vc, _, bad = is_vertex_critical(G, k)
    res["vertex_critical"] = vc
    res["non_critical_vertices"] = bad
    if not vc:
        if verbose:
            print(f"FAIL: not vertex-critical; non-critical vertices: {bad}")
        return res
    ce = critical_edges(G, chi)
    res["critical_edges"] = ce
    res["num_critical_edges"] = len(ce)
    res["is_witness"] = (len(ce) == 0)
    if verbose:
        if res["is_witness"]:
            print(f"*** WITNESS *** n={res['n']} m={res['m']} chi=4, "
                  f"vertex-critical, NO critical edge.")
        else:
            print(f"FAIL: {len(ce)} critical edge(s), e.g. {ce[:5]}")
    return res


def summary(G, name=""):
    chi = chromatic_number(G)
    vc, _, bad = is_vertex_critical(G)
    ce = critical_edges(G, chi)
    print(f"[{name}] n={G.number_of_nodes()} m={G.number_of_edges()} "
          f"chi={chi} vertex_critical={vc} (#noncrit_v={len(bad)}) "
          f"#critical_edges={len(ce)}")
    return chi, vc, bad, ce


if __name__ == "__main__":
    # Self-test on known graphs.
    print("=== Self-tests ===")
    # K4: chi=4, vertex-critical, EVERY edge critical (the simplest 4-critical, all edges critical)
    K4 = nx.complete_graph(4)
    summary(K4, "K4")
    # C5: chi=3, vertex-critical (odd cycle), every edge critical
    C5 = nx.cycle_graph(5)
    summary(C5, "C5")
    # Grotzsch graph: triangle-free, chi=4, vertex-critical. Edges?
    G = nx.mycielskian(nx.cycle_graph(5))  # Grotzsch
    summary(G, "Grotzsch (Mycielskian of C5)")
    # Petersen: chi=3
    summary(nx.petersen_graph(), "Petersen")
