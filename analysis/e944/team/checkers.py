"""
e944 independent predicate checkers (hunter).

Target predicate (EXACT mirror of FormalConjectures/.../Coloring.lean + 944.lean):

  IsCriticalEdges G edges := chi(G.deleteEdges edges) < chi(G)
  IsCriticalEdge  G e     := IsCriticalEdges G {e}
  Subgraph.IsCriticalVertex G v := chi(G - v) < chi(G)
  IsCritical G k := chi(G) = k  AND  forall v, chi(G - v) < chi(G)
  IsErdos944 G k r := IsCritical G k  AND  (forall edge-set S, IsCriticalEdges G S -> r < |S|)

For k=4, r=1 the target is:
  - chi(G) = 4
  - every vertex critical: chi(G - v) = 3 for all v  (since G is 4-chromatic, G-v has chi <= 4;
    "critical" means chi(G-v) < 4, i.e. <= 3; and a 4-critical graph cannot have chi(G-v) <= 2
    on the whole, but we only require < 4)
  - NO critical single edge: for every edge e, chi(G - e) = 4  (deleting one edge does NOT drop chi
    below 4). Equivalently every critical edge-set has size >= 2 (size > 1).
    [Empty set is never critical since deleteEdges {} = G, chi < chi is false. So the binding
     constraint is exactly "no single edge is critical".]

Two INDEPENDENT chi-computations:
  (A) chromatic_number_exact: pure-python backtracking exact graph coloring (no SAT).
  (B) is_k_colorable_sat:     SAT encoding of k-colorability via python-sat (Cadical).

Cross-validated against each other on every graph touched during search.
"""
from itertools import combinations
import networkx as nx


# ---------------------------------------------------------------------------
# (A) Pure-python EXACT chromatic number via backtracking (independent of SAT)
# ---------------------------------------------------------------------------

def is_k_colorable_backtrack(adj, n, k):
    """Exact k-colorability by DSATUR-ordered backtracking. adj: list of int bitmasks.
    Returns True iff the graph on n vertices with adjacency `adj` is properly k-colorable.
    No external solver. Pure combinatorial search."""
    if k <= 0:
        return n == 0
    if k >= n:
        return True  # n vertices always colorable with n colors
    color = [-1] * n
    # order vertices by descending degree for a tighter search tree
    order = sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))
    pos_of = [0] * n
    for i, v in enumerate(order):
        pos_of[v] = i

    def backtrack(idx, max_used):
        if idx == n:
            return True
        v = order[idx]
        # forbidden colors from already-colored neighbors
        forbidden = 0
        nb = adj[v]
        while nb:
            low = nb & (-nb)
            u = low.bit_length() - 1
            if color[u] >= 0:
                forbidden |= (1 << color[u])
            nb ^= low
        # symmetry break: only try colors up to max_used+1 (and < k)
        limit = min(max_used + 1, k - 1)
        for c in range(limit + 1):
            if not (forbidden >> c) & 1:
                color[v] = c
                if backtrack(idx + 1, max(max_used, c)):
                    return True
                color[v] = -1
        return False

    return backtrack(0, -1)


def chromatic_number_exact(adj, n):
    """Exact chromatic number by trying k = 1, 2, 3, ... (pure python)."""
    if n == 0:
        return 0
    # any edge present -> chi >= 2
    for k in range(1, n + 1):
        if is_k_colorable_backtrack(adj, n, k):
            return k
    return n


# ---------------------------------------------------------------------------
# (B) SAT-based k-colorability (independent code path, python-sat / Cadical)
# ---------------------------------------------------------------------------

def is_k_colorable_sat(edges, n, k):
    """k-colorability via SAT. edges: iterable of (u,v) with u<v. Returns bool.
    Variable x(v,c) = v gets color c, var id = v*k + c + 1."""
    from pysat.solvers import Cadical195
    if k <= 0:
        return n == 0
    if n == 0:
        return True

    def var(v, c):
        return v * k + c + 1

    solver = Cadical195()
    # each vertex gets at least one color
    for v in range(n):
        solver.add_clause([var(v, c) for c in range(k)])
        # at most one color (optional but tightens; pairwise)
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                solver.add_clause([-var(v, c1), -var(v, c2)])
    # adjacent vertices differ
    for (u, v) in edges:
        for c in range(k):
            solver.add_clause([-var(u, c), -var(v, c)])
    sat = solver.solve()
    solver.delete()
    return sat


def chromatic_number_sat(edges, n):
    """Exact chromatic number via SAT (independent of the backtracking path)."""
    if n == 0:
        return 0
    edges = list(edges)
    for k in range(1, n + 1):
        if is_k_colorable_sat(edges, n, k):
            return k
    return n


# ---------------------------------------------------------------------------
# Graph representation helpers
# ---------------------------------------------------------------------------

def edges_to_adj(edges, n):
    """edges: list of (u,v). Returns adjacency bitmask list of length n."""
    adj = [0] * n
    for (u, v) in edges:
        adj[u] |= (1 << v)
        adj[v] |= (1 << u)
    return adj


def adj_remove_vertex(adj, n, v):
    """Return (adj', n', relabel) for G - v with vertices relabeled 0..n-2."""
    keep = [u for u in range(n) if u != v]
    idx = {u: i for i, u in enumerate(keep)}
    new_adj = [0] * (n - 1)
    for u in keep:
        nb = adj[u]
        while nb:
            low = nb & (-nb)
            w = low.bit_length() - 1
            if w != v:
                new_adj[idx[u]] |= (1 << idx[w])
            nb ^= low
    return new_adj, n - 1


def edges_remove_edge(edges, e):
    """Return edge list with edge e=(a,b) removed (canonical, a<b)."""
    a, b = min(e), max(e)
    return [(u, v) for (u, v) in edges if not (min(u, v) == a and max(u, v) == b)]


# ---------------------------------------------------------------------------
# Target predicates (using BACKTRACK chi by default; SAT used for cross-check)
# ---------------------------------------------------------------------------

def chi_bt(edges, n):
    return chromatic_number_exact(edges_to_adj(edges, n), n)


def is_vertex_critical(edges, n, k, chi_fn=chi_bt):
    """chi(G)=k and for all v: chi(G-v) < k."""
    if chi_fn(edges, n) != k:
        return False
    adj = edges_to_adj(edges, n)
    for v in range(n):
        sub_adj, sub_n = adj_remove_vertex(adj, n, v)
        # convert sub_adj back to edges for a uniform chi call
        sub_edges = []
        for a in range(sub_n):
            nb = sub_adj[a]
            while nb:
                low = nb & (-nb)
                b = low.bit_length() - 1
                if a < b:
                    sub_edges.append((a, b))
                nb ^= low
        if chromatic_number_exact(sub_adj, sub_n) >= k:
            return False
    return True


def has_no_critical_edge(edges, n, k, chi_fn=chi_bt):
    """True iff for every edge e, chi(G - e) = k (no single edge drops chi below k)."""
    for e in edges:
        sub_edges = edges_remove_edge(edges, e)
        if chi_fn(sub_edges, n) < k:
            return False
    return True


def is_erdos944_k_r1(edges, n, k=4, chi_fn=chi_bt):
    """Full target predicate for r=1: k-vertex-critical AND no critical single edge."""
    return is_vertex_critical(edges, n, k, chi_fn) and has_no_critical_edge(edges, n, k, chi_fn)
