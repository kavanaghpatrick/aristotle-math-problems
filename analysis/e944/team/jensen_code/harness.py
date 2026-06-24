"""
E944 verification harness — jensen.

Checks for a finite simple graph G (networkx.Graph):
  - chromatic_number(G): exact χ via ILP (pulp) with a fast greedy/clique bracket,
    plus an independent backtracking exact χ for cross-validation.
  - is_vertex_critical(G, k): χ(G)=k AND for every vertex v, χ(G - v) < k.
  - has_critical_edge(G): some edge e with χ(G - e) < χ(G).
  - is_erdos944_4_1(G): χ=4, vertex-critical, AND no critical edge.

Two independent exact χ engines are provided and MUST agree (assert) so we never
trust a single buggy colorer. The Dirac/E944 target object is:
    χ(G)=4, every vertex critical, NO single edge critical.

Vocab lock (per gallai/archivist): IsCritical = VERTEX-critical, not edge-critical.
"""
from __future__ import annotations
import itertools
import networkx as nx


# ---------- Exact chromatic number, engine A: backtracking with pruning ----------

def chromatic_number_backtrack(G: nx.Graph) -> int:
    """Exact χ by iterative-deepening greedy color count with backtracking.
    Returns χ for a finite simple graph. Handles empty graph (χ=0) and
    edgeless nonempty graph (χ=1)."""
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if G.number_of_edges() == 0:
        return 1
    nodes = list(G.nodes())
    # Order by degree descending (helps pruning).
    nodes.sort(key=lambda v: G.degree(v), reverse=True)
    adj = {v: set(G.neighbors(v)) for v in nodes}

    # Lower bound: a clique size (greedy). Upper bound: greedy coloring.
    def greedy_colors():
        color = {}
        for v in nodes:
            used = {color[u] for u in adj[v] if u in color}
            c = 0
            while c in used:
                c += 1
            color[v] = c
        return max(color.values()) + 1

    ub = greedy_colors()

    def can_color(k: int) -> bool:
        color = {}

        def bt(i: int) -> bool:
            if i == len(nodes):
                return True
            v = nodes[i]
            used = {color[u] for u in adj[v] if u in color}
            # Symmetry break: only try colors up to 1 + max used so far globally.
            max_used = max(color.values()) + 1 if color else 0
            limit = min(k, max_used + 1)
            for c in range(limit):
                if c not in used:
                    color[v] = c
                    if bt(i + 1):
                        return True
                    del color[v]
            return False

        return bt(0)

    # Find smallest k in [1, ub] that colors.
    for k in range(1, ub + 1):
        if can_color(k):
            return k
    return ub


# ---------- Exact chromatic number, engine B: independent DSATUR + exact search ----------

def chromatic_number_exact_B(G: nx.Graph) -> int:
    """Independent exact χ: lower bound via maximum clique, then exhaustive
    k-coloring feasibility using a different node ordering (DSATUR-like) so any
    bug in engine A is unlikely to be shared."""
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if G.number_of_edges() == 0:
        return 1
    nodes = list(G.nodes())
    adj = {v: set(G.neighbors(v)) for v in nodes}

    # Max clique lower bound (networkx, exact for small graphs).
    try:
        lb = nx.graph_clique_number(G)
    except Exception:
        lb = max((len(c) for c in nx.find_cliques(G)), default=1)

    def feasible(k: int) -> bool:
        # DSATUR order, backtracking.
        color = {}

        def select():
            # pick uncolored vertex with max saturation, tie-break by degree.
            best, best_key = None, None
            for v in nodes:
                if v in color:
                    continue
                sat = len({color[u] for u in adj[v] if u in color})
                key = (sat, G.degree(v))
                if best_key is None or key > best_key:
                    best, best_key = v, key
            return best

        def bt(count):
            if count == n:
                return True
            v = select()
            used = {color[u] for u in adj[v] if u in color}
            max_used = max(color.values()) + 1 if color else 0
            limit = min(k, max_used + 1)
            for c in range(limit):
                if c not in used:
                    color[v] = c
                    if bt(count + 1):
                        return True
                    del color[v]
            return False

        return bt(0)

    k = lb
    while not feasible(k):
        k += 1
        if k > n:
            return n
    return k


def chromatic_number(G: nx.Graph) -> int:
    """Cross-validated exact χ: both engines must agree."""
    a = chromatic_number_backtrack(G)
    b = chromatic_number_exact_B(G)
    assert a == b, f"χ engines disagree: backtrack={a}, exactB={b}"
    return a


# ---------- Criticality predicates ----------

def is_vertex_critical(G: nx.Graph, k: int) -> bool:
    """χ(G)=k AND deleting any single vertex drops χ below k."""
    if chromatic_number(G) != k:
        return False
    for v in list(G.nodes()):
        H = G.copy()
        H.remove_node(v)
        if chromatic_number(H) >= k:
            return False
    return True


def critical_edges(G: nx.Graph):
    """Return list of edges e such that χ(G - e) < χ(G)."""
    chi = chromatic_number(G)
    out = []
    for (u, v) in list(G.edges()):
        H = G.copy()
        H.remove_edge(u, v)
        if chromatic_number(H) < chi:
            out.append((u, v))
    return out


def has_critical_edge(G: nx.Graph) -> bool:
    return len(critical_edges(G)) > 0


def is_erdos944(G: nx.Graph, k: int = 4) -> dict:
    """Full E944 check. Returns a dict report.
    Witness condition (k, r=1): χ=k, vertex-critical, NO critical edge."""
    chi = chromatic_number(G)
    rep = {
        "n": G.number_of_nodes(),
        "m": G.number_of_edges(),
        "chi": chi,
        "chi_is_k": chi == k,
    }
    if chi != k:
        rep["vertex_critical"] = None
        rep["num_critical_edges"] = None
        rep["is_witness"] = False
        return rep
    vc = is_vertex_critical(G, k)
    rep["vertex_critical"] = vc
    ce = critical_edges(G)
    rep["num_critical_edges"] = len(ce)
    rep["critical_edges_sample"] = ce[:5]
    rep["is_witness"] = vc and (len(ce) == 0)
    return rep


# ---------- Known-graph sanity checks ----------

def _self_test():
    # K4: χ=4, vertex-critical, EVERY edge critical → not a witness.
    K4 = nx.complete_graph(4)
    r = is_erdos944(K4, 4)
    assert r["chi"] == 4 and r["vertex_critical"] is True
    assert r["num_critical_edges"] == 6, r
    assert r["is_witness"] is False

    # C5 (odd cycle): χ=3, vertex-critical at k=3, every edge critical.
    C5 = nx.cycle_graph(5)
    assert chromatic_number(C5) == 3
    assert is_vertex_critical(C5, 3)
    assert len(critical_edges(C5)) == 5

    # Petersen: χ=3.
    P = nx.petersen_graph()
    assert chromatic_number(P) == 3

    # K_{3,3}: χ=2.
    assert chromatic_number(nx.complete_bipartite_graph(3, 3)) == 2

    # Grötzsch graph: triangle-free, χ=4, vertex-critical and EDGE-critical
    # (it is 4-edge-critical) → has critical edges.
    Gr = nx.mycielskian(nx.cycle_graph(5))  # Mycielskian of C5 = Grötzsch
    assert chromatic_number(Gr) == 4, chromatic_number(Gr)
    assert is_vertex_critical(Gr, 4)
    assert has_critical_edge(Gr)  # Grötzsch is edge-critical → not a witness

    print("HARNESS SELF-TEST PASSED")
    print("  K4: witness?", is_erdos944(K4, 4)["is_witness"], "(expect False)")
    print("  Grotzsch (Mycielskian C5): chi=4 vertex-crit, critical edges =",
          len(critical_edges(Gr)), "(expect > 0, it's edge-critical)")


if __name__ == "__main__":
    _self_test()
