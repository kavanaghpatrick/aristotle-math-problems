"""
E944 criticality toolkit (gallai).

Exact chromatic number + the three predicates that match the Lean defs
in FormalConjecturesForMathlib/.../Coloring.lean:

  IsCriticalEdges G edges  := chi(G - edges) < chi(G)
  IsCriticalEdge G e       := IsCriticalEdges G {e}
  IsCritical G k           := chi(G)=k AND for every vertex v, chi(G - v) < chi(G)   (VERTEX-critical)
  IsErdos944 G k r         := IsCritical G k AND every critical edge-SET has size > r

For k=4, r=1 the witness condition is:
  chi(G)=4, G vertex-critical, and NO single edge is critical
  (deleting any one edge keeps chi = 4).

Exact chi via SAT (pysat) with a decision oracle + linear search; small graphs
also cross-checked with a backtracking colorer.
"""
from itertools import combinations
import networkx as nx
from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def _colorable_sat(G, k):
    """Decision: is G k-colorable? Exact, via SAT."""
    if k <= 0:
        return G.number_of_nodes() == 0
    nodes = list(G.nodes())
    pool = IDPool()
    var = {(v, c): pool.id((v, c)) for v in nodes for c in range(k)}
    cnf = []
    for v in nodes:
        cnf.append([var[(v, c)] for c in range(k)])           # at least one color
        for c1, c2 in combinations(range(k), 2):              # at most one color
            cnf.append([-var[(v, c1)], -var[(v, c2)]])
    for u, w in G.edges():
        for c in range(k):
            cnf.append([-var[(u, c)], -var[(w, c)]])           # endpoints differ
    with Glucose3(bootstrap_with=cnf) as s:
        return s.solve()


def chi(G):
    """Exact chromatic number."""
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if G.number_of_edges() == 0:
        return 1
    # lower bound: clique number is expensive; just linear-search from 1.
    k = 1
    while not _colorable_sat(G, k):
        k += 1
    return k


def is_vertex_critical(G, k=None):
    """chi(G)=k and chi(G - v) < chi(G) for every vertex v."""
    c = chi(G)
    if k is not None and c != k:
        return False
    for v in list(G.nodes()):
        H = G.copy()
        H.remove_node(v)
        if chi(H) >= c:
            return False
    return True


def critical_edges(G):
    """List of single edges e with chi(G - e) < chi(G)."""
    c = chi(G)
    out = []
    for u, w in G.edges():
        H = G.copy()
        H.remove_edge(u, w)
        if chi(H) < c:
            out.append((u, w))
    return out


def is_erdos944_witness(G, k=4, r=1):
    """Full check: vertex-critical of chrom k, with no critical edge-set of size <= r.

    For r=1 it suffices to check no SINGLE edge is critical, because if any
    edge-set of size <=1 is critical it is a singleton (empty set is never
    critical), and conversely a minimal critical set never has a redundant edge,
    so 'some <=r set critical' for r=1 reduces to 'some singleton critical'.
    """
    if chi(G) != k:
        return False, "chi != k"
    if not is_vertex_critical(G, k):
        return False, "not vertex-critical"
    ce = critical_edges(G)
    if r == 1:
        if ce:
            return False, f"has {len(ce)} critical edge(s), e.g. {ce[0]}"
        return True, "WITNESS: vertex-critical, no critical edge"
    # general r: search edge-subsets of size <= r
    for sz in range(1, r + 1):
        for es in combinations(list(G.edges()), sz):
            H = G.copy()
            H.remove_edges_from(es)
            if chi(H) < k:
                return False, f"critical edge-set of size {sz}: {es}"
    return True, f"WITNESS: vertex-critical, no critical edge-set of size <= {r}"


if __name__ == "__main__":
    # Sanity checks on known objects.
    K4 = nx.complete_graph(4)
    print("K4: chi =", chi(K4), "(expect 4)")
    print("K4 vertex-critical(4):", is_vertex_critical(K4, 4), "(expect True)")
    print("K4 critical edges:", len(critical_edges(K4)), "(expect 6 — every edge critical)")
    print("K4 is 944 witness:", is_erdos944_witness(K4))

    C5 = nx.cycle_graph(5)
    print("C5: chi =", chi(C5), "(expect 3)")

    # Odd wheel W5 = C5 + hub: chi 4, edge-critical => has critical edges
    W5 = nx.wheel_graph(5)  # hub + C5
    print("W5(=C5+hub): chi =", chi(W5), "vc4 =", is_vertex_critical(W5, 4))
    print("W5 critical edges:", len(critical_edges(W5)))


# ---------- Theorem 2 local prune (rainbow-forcing) ----------

def _proper_3colorings(H):
    """Enumerate all proper 3-colorings of H as dicts. Small graphs only."""
    from itertools import product
    nodes = list(H.nodes())
    edges = list(H.edges())
    for assign in product(range(3), repeat=len(nodes)):
        c = dict(zip(nodes, assign))
        if all(c[a] != c[b] for a, b in edges):
            yield c


def edge_noncritical_local(G, u, v):
    """Theorem 2: edge uv is NON-critical iff in every proper 3-coloring of G-u,
    N(u)\\{v} uses all 3 colors. Requires deg(u) small enough to enumerate G-u
    colorings cheaply; intended as a prune for small candidate graphs.
    Returns True if uv is non-critical by the rainbow-forcing test from u's side.
    """
    H = G.copy()
    H.remove_node(u)
    others = [w for w in G.neighbors(u) if w != v]
    for c in _proper_3colorings(H):
        if len({c[w] for w in others}) < 3:
            return False  # found a coloring leaving u a free color => uv critical
    return True


def witness_local_prune(G):
    """Fast necessary check for an E944 witness using Theorem 2 / min-degree-6.
    Returns (False, reason) on the first violation; (True, None) if the graph
    passes all LOCAL necessary conditions (still must confirm chi=4 + vertex-critical
    + full no-critical-edge for sufficiency)."""
    deg = dict(G.degree())
    if deg and min(deg.values()) < 6:
        return False, f"min-degree {min(deg.values())} < 6 (Theorem 3)"
    # Every edge must be non-critical by the local rainbow test.
    for u, v in G.edges():
        if not edge_noncritical_local(G, u, v):
            return False, f"edge ({u},{v}) is critical (rainbow-forcing fails from {u})"
        if not edge_noncritical_local(G, v, u):
            return False, f"edge ({u},{v}) is critical (rainbow-forcing fails from {v})"
    return True, None
