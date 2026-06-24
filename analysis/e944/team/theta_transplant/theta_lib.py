"""Lovász theta via SDP (cvxpy/Clarabel high-accuracy). Conventions:
theta(G) = independence-side (alpha <= theta(G) <= chi(complement G)).
For chromatic bounds on G use theta(complement(G)) <= chi(G)... NO:
sandwich: alpha(G) <= theta(G) <= chibar(G)=chi(Gbar). So chi(G) >= theta(Gbar).
We expose theta_of_edges(n, edge_set) where edge_set are the EDGES of the graph
whose theta we compute (X_ij = 0 forced on edges).
"""
import numpy as np
import cvxpy as cp
import itertools


def theta_of(n, edges):
    """Lovasz theta of graph H=(n, edges). max <J,X> ; tr X=1 ; X_ij=0 (ij in E); X psd."""
    X = cp.Variable((n, n), symmetric=True)
    cons = [X >> 0, cp.trace(X) == 1]
    for (i, j) in edges:
        cons.append(X[i, j] == 0)
    prob = cp.Problem(cp.Maximize(cp.sum(X)), cons)
    val = prob.solve(solver=cp.CLARABEL)
    return float(val)


def complement_edges(n, edges):
    es = set(frozenset(e) for e in edges)
    return [(i, j) for i, j in itertools.combinations(range(n), 2)
            if frozenset((i, j)) not in es]


def chrom_theta(n, edges):
    """theta(Gbar) — the SDP lower bound on chi(G)."""
    return theta_of(n, complement_edges(n, edges))


def chrom_theta_minus_edge(n, edges, e):
    """theta(complement(G-e)) = theta(Gbar + e): SDP lower bound on chi(G-e)."""
    es = [tuple(x) for x in edges if frozenset(x) != frozenset(e)]
    return theta_of(n, complement_edges(n, es))


def is_3col(n, edges, k=3):
    """exact k-colorability by backtracking with degree-ordering."""
    adj = [0] * n
    for i, j in edges:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    order = sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))
    color = [-1] * n

    def bt(idx, used):
        if idx == n:
            return True
        v = order[idx]
        seen = set()
        for u in range(n):
            if (adj[v] >> u) & 1 and color[u] >= 0:
                seen.add(color[u])
        for c in range(min(used + 1, k)):
            if c in seen:
                continue
            color[v] = c
            if bt(idx + 1, max(used, c + 1)):
                return True
            color[v] = -1
        return False

    return bt(0, 0)


def g6_to_edges(line):
    line = line.strip()
    data = [ord(c) - 63 for c in line]
    n = data[0]
    bits = []
    for d in data[1:]:
        for b in range(5, -1, -1):
            bits.append((d >> b) & 1)
    edges = []
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                edges.append((i, j))
            idx += 1
    return n, edges
