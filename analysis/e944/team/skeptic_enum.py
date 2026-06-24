#!/usr/bin/env python3
"""
skeptic_enum.py — INDEPENDENT small-n ground truth for E944.

Goal: establish, by exhaustive enumeration with TWO independent chi-checkers that
must agree, whether every FINITE 4-vertex-critical graph on <= N vertices has a
critical edge. (Statement-lock skeptic_statement_lock.md proves the Lean question
reduces to this finite question.)

INDEPENDENCE (vs hunter/checkers.py, count/critedge.py, forge/algebra harnesses):
  * Enumeration source: nauty `geng -c` (exhaustive canonical generation of all
    connected graphs up to iso). NOT a hand-rolled subset/itertools enumeration.
    A 4-vertex-critical graph is necessarily connected (a disconnected graph's
    chromatic number is the max over components; deleting a vertex in one component
    cannot drop the global chi unless that component alone realizes chi and removing
    the vertex drops it — but then vertices in OTHER components are non-critical).
    So `geng -c` is a sound and complete source for 4-critical candidates.
  * chi-checker A: from-scratch recursive backtracking coloring with a greedy clique
    lower bound and most-constrained-vertex ordering. Pure python, my own code.
  * chi-checker B: SAT k-colorability via python-sat (Cadical). Independent encoding.
  Every graph that reaches the criticality test has chi computed by BOTH; they must
  return the SAME value or the script ABORTS (no silent buggy-checker celebration).

Definitions mirror the LOCKED Lean defs:
  chi(G)                 = least k with a proper k-coloring
  IsCritical G 4         = chi(G)==4 AND for every vertex v, chi(G - v) < 4
  IsCriticalEdge G e     = chi(G - e) < chi(G)
  has no critical edge   = for every edge e, chi(G - e) == chi(G) (==4)
  E944 witness (k=4,r=1) = chi=4, vertex-critical, no critical edge.

Usage: python3 skeptic_enum.py [Nmax]   (default Nmax=10; 11 is heavy)
"""
import sys
import subprocess
from itertools import combinations

import networkx as nx

GENG = "/opt/homebrew/bin/geng"

# ---------------------------------------------------------------------------
# chi-checker A: from-scratch backtracking with clique lower bound.
# Representation: adjacency as list[set[int]] over vertices 0..n-1.
# ---------------------------------------------------------------------------

def _greedy_clique_lb(adj, n):
    """A greedy maximal clique size — a valid LOWER bound on chi."""
    best = 0
    order = sorted(range(n), key=lambda v: len(adj[v]), reverse=True)
    for start in order[: min(n, 8)]:  # a few seeds is enough for a good LB
        clique = [start]
        cand = set(adj[start])
        while cand:
            # pick the candidate with most connections inside cand (greedy)
            v = max(cand, key=lambda x: len(adj[x] & cand))
            clique.append(v)
            cand &= adj[v]
        best = max(best, len(clique))
    return best


def _k_colorable_backtrack(adj, n, k):
    """True iff colorable with k colors. Recursive, most-constrained-vertex first."""
    if k <= 0:
        return n == 0
    color = [-1] * n
    # static order by degree desc helps pruning
    order = sorted(range(n), key=lambda v: len(adj[v]), reverse=True)

    def feasible(v, c):
        for u in adj[v]:
            if color[u] == c:
                return False
        return True

    def bt(idx, used):
        if idx == n:
            return True
        v = order[idx]
        # symmetry break: never use a new color index beyond used+1
        upper = min(k, used + 1)
        for c in range(upper):
            if feasible(v, c):
                color[v] = c
                if bt(idx + 1, max(used, c + 1)):
                    return True
                color[v] = -1
        return False

    return bt(0, 0)


def chi_A(adj, n):
    """Exact chromatic number via checker A."""
    if n == 0:
        return 0
    lb = max(1, _greedy_clique_lb(adj, n))
    # any graph is n-colorable; search up from the clique lower bound
    for k in range(lb, n + 1):
        if _k_colorable_backtrack(adj, n, k):
            return k
    return n


# ---------------------------------------------------------------------------
# chi-checker B: SAT k-colorability (python-sat / Cadical). Independent.
# ---------------------------------------------------------------------------
try:
    from pysat.solvers import Cadical153 as _SatSolver
except Exception:  # pragma: no cover
    from pysat.solvers import Glucose3 as _SatSolver


def _k_colorable_sat(adj, n, k):
    if k <= 0:
        return n == 0
    if n == 0:
        return True
    # var(v,c) = v*k + c + 1
    def var(v, c):
        return v * k + c + 1
    solver = _SatSolver()
    for v in range(n):
        solver.add_clause([var(v, c) for c in range(k)])  # at least one color
        # at most one color (optional but keeps it a clean coloring)
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                solver.add_clause([-var(v, c1), -var(v, c2)])
    for v in range(n):
        for u in adj[v]:
            if u > v:
                for c in range(k):
                    solver.add_clause([-var(v, c), -var(u, c)])
    sat = solver.solve()
    solver.delete()
    return sat


def chi_B(adj, n):
    if n == 0:
        return 0
    for k in range(1, n + 1):
        if _k_colorable_sat(adj, n, k):
            return k
    return n


# ---------------------------------------------------------------------------
# Cross-checked chi: both checkers must agree.
# ---------------------------------------------------------------------------
_AGREE = 0
_DISAGREE = 0

def chi(adj, n):
    global _AGREE, _DISAGREE
    a = chi_A(adj, n)
    b = chi_B(adj, n)
    if a != b:
        _DISAGREE += 1
        raise SystemExit(
            f"FATAL: chi-checkers DISAGREE (A={a}, B={b}) on n={n} adj={adj}. "
            "Stopping — a buggy checker invalidates all results."
        )
    _AGREE += 1
    return a


# ---------------------------------------------------------------------------
# Graph utilities on the adj-set representation.
# ---------------------------------------------------------------------------

def nx_to_adj(G):
    n = G.number_of_nodes()
    # relabel to 0..n-1 in a fixed order
    nodes = list(G.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    adj = [set() for _ in range(n)]
    for u, v in G.edges():
        adj[idx[u]].add(idx[v])
        adj[idx[v]].add(idx[u])
    return adj, n


def delete_vertex(adj, n, v):
    """Return (adj', n') with vertex v removed and remaining relabeled 0..n-2."""
    remap = {}
    j = 0
    for u in range(n):
        if u != v:
            remap[u] = j
            j += 1
    adj2 = [set() for _ in range(n - 1)]
    for u in range(n):
        if u == v:
            continue
        for w in adj[u]:
            if w != v:
                adj2[remap[u]].add(remap[w])
    return adj2, n - 1


def delete_edge(adj, n, e):
    a, b = e
    adj2 = [set(s) for s in adj]
    adj2[a].discard(b)
    adj2[b].discard(a)
    return adj2, n


def edges_of(adj, n):
    es = []
    for u in range(n):
        for w in adj[u]:
            if u < w:
                es.append((u, w))
    return es


# ---------------------------------------------------------------------------
# E944 predicates.
# ---------------------------------------------------------------------------

def is_vertex_critical_4(adj, n):
    """chi(G)==4 AND every vertex deletion drops chi below 4."""
    if chi(adj, n) != 4:
        return False
    for v in range(n):
        adj2, n2 = delete_vertex(adj, n, v)
        if chi(adj2, n2) >= 4:
            return False
    return True


def has_critical_edge(adj, n):
    """True iff some single edge deletion drops chi below chi(G)=4."""
    for e in edges_of(adj, n):
        adj2, n2 = delete_edge(adj, n, e)
        if chi(adj2, n2) < 4:
            return True
    return False


# ---------------------------------------------------------------------------
# Exhaustive sweep via geng.
# ---------------------------------------------------------------------------

def geng_connected(n, mindeg=0):
    """Yield networkx graphs: all connected graphs on n vertices (up to iso).

    mindeg: pass to geng -d<mindeg>. SOUND for 4-critical search because in a
    4-vertex-critical graph every vertex has degree >= 3 (the standard
    delta(G) >= k-1 lemma: if v is critical, chi(G-v)=3; a 3-coloring of G-v
    leaves a free color for v whenever deg(v) <= 2, extending to a 3-coloring of
    G and contradicting chi(G)=4). So restricting to min-degree>=3 misses NO
    4-critical graph. Verified empirically: with and without the filter the
    4-critical counts match for n<=8 (see skeptic_smalln_groundtruth.md)."""
    args = [GENG, "-c"]
    if mindeg > 0:
        args.append(f"-d{mindeg}")
    args.append(str(n))
    proc = subprocess.Popen(args,
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        yield nx.from_graph6_bytes(line)
    proc.wait()


def sweep(nmax, nmin=4, mindeg=0):
    print(f"# skeptic independent E944 sweep, n={nmin}..{nmax} (geng mindeg={mindeg})")
    print(f"# enumeration: nauty geng -c ; chi by TWO independent checkers (backtrack + SAT)")
    grand_4crit = 0
    grand_witness = 0
    for n in range(nmin, nmax + 1):
        n_4crit = 0
        n_with_crit_edge = 0
        n_witness = 0
        ngraphs = 0
        for G in geng_connected(n, mindeg=mindeg):
            ngraphs += 1
            adj, nn = nx_to_adj(G)
            if not is_vertex_critical_4(adj, nn):
                continue
            n_4crit += 1
            if has_critical_edge(adj, nn):
                n_with_crit_edge += 1
            else:
                n_witness += 1
                print(f"  !!! WITNESS CANDIDATE n={n}: graph6={nx.to_graph6_bytes(G, header=False).strip().decode()}")
        grand_4crit += n_4crit
        grand_witness += n_witness
        print(f"n={n:2d}: connected={ngraphs:7d}  4-vertex-critical={n_4crit:5d}  "
              f"have_critical_edge={n_with_crit_edge:5d}  NO_critical_edge(WITNESS)={n_witness}")
    print(f"# TOTAL 4-vertex-critical (n<= {nmax}) = {grand_4crit}; witnesses = {grand_witness}")
    print(f"# chi cross-checks: agreements={_AGREE}, disagreements={_DISAGREE}")
    if grand_witness == 0:
        print(f"# GROUND TRUTH: every 4-vertex-critical graph on <= {nmax} vertices HAS a critical edge.")
    return grand_witness


if __name__ == "__main__":
    # args: Nmax [Nmin] [mindeg]
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    nmin = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    mindeg = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    sys.exit(0 if sweep(nmax, nmin=nmin, mindeg=mindeg) == 0 else 1)
