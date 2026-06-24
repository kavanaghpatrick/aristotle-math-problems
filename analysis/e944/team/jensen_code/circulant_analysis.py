"""
Dissect the Jensen 2002 / Skottova-Steiner 2025 circulant construction and
find EXACTLY where it breaks at k=4.

Construction G_{k,m,q} (Skottova-Steiner 2508.08703, "modification of Jensen"):
  N = q * n_{k,m} + 1  vertices (q even), circulant on Z_N with v_0 the apex.
  period  n_{k,m} = (k-1)m       if k odd
                  = 2(k-1)m      if k even
  Distance set D = D1 ∪ D2 ∪ D3 (cyclic distances in Z_N):
    D1 = {1,3,5,...,2m-1}
    D2 (k odd) : ∪_{q'=0}^{q/2-1} ([2m, (k-3)m+1] + q'*n)
    D2 (k even): ∪_{q'=0}^{q/2-1} ([2m, (k-4)m+2] + q'*n)
    D3 (k odd) : ∅
    D3 (k even): ∪_{q'=0}^{q/2-1} ([(k+2)m-1, (2k-4)m+1] + q'*n)
  ([a,b] = integers a..b inclusive; empty if a>b.)

We compute the intervals symbolically for each k to see which intervals collapse
to EMPTY at k=4, then build small instances and verify with the harness.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges, is_erdos944


def interval(a, b):
    """Integers a..b inclusive; empty list if a > b."""
    return list(range(a, b + 1)) if a <= b else []


def period(k, m):
    return (k - 1) * m if k % 2 == 1 else 2 * (k - 1) * m


def D2_base_interval(k, m):
    """The base interval [a,b] of D2 (before q'-shifts)."""
    if k % 2 == 1:
        return (2 * m, (k - 3) * m + 1)
    else:
        return (2 * m, (k - 4) * m + 2)


def D3_base_interval(k, m):
    """The base interval [a,b] of D3 (k even only); None for k odd."""
    if k % 2 == 1:
        return None
    return ((k + 2) * m - 1, (2 * k - 4) * m + 1)


def symbolic_report(k, m):
    n = period(k, m)
    d1 = interval(1, 2 * m - 1)[::2] if False else list(range(1, 2 * m, 2))
    a2, b2 = D2_base_interval(k, m)
    d2 = interval(a2, b2)
    d3i = D3_base_interval(k, m)
    print(f"--- k={k}, m={m} ---  (k {'odd' if k%2 else 'even'})")
    print(f"  period n_{{k,m}} = {n}")
    print(f"  D1 = odd numbers 1..{2*m-1}  -> {list(range(1,2*m,2))}")
    print(f"  D2 base interval [{a2}, {b2}]  -> {'EMPTY' if a2>b2 else d2}")
    if d3i is None:
        print(f"  D3 = (empty, k odd)")
    else:
        a3, b3 = d3i
        d3 = interval(a3, b3)
        print(f"  D3 base interval [{a3}, {b3}]  -> {'EMPTY' if a3>b3 else d3}")
    return n


def build_Gkmq(k, m, q):
    """Build G_{k,m,q} as a circulant on Z_N (N = q*n+1). v_0 is index 0 (apex)."""
    assert q % 2 == 0, "q must be even"
    n = period(k, m)
    N = q * n + 1
    # base distance set
    D = set(range(1, 2 * m, 2))  # D1 odd
    a2, b2 = D2_base_interval(k, m)
    base2 = interval(a2, b2)
    for qp in range(q // 2):
        for d in base2:
            D.add(d + qp * n)
    d3i = D3_base_interval(k, m)
    if d3i is not None:
        a3, b3 = d3i
        base3 = interval(a3, b3)
        for qp in range(q // 2):
            for d in base3:
                D.add(d + qp * n)
    # cyclic distances must be in [1, N//2]; reduce
    Dred = set()
    for d in D:
        dd = d % N
        dd = min(dd, N - dd)
        if dd >= 1:
            Dred.add(dd)
    G = nx.Graph()
    G.add_nodes_from(range(N))
    for i in range(N):
        for d in Dred:
            G.add_edge(i, (i + d) % N)
    return G, N, Dred


if __name__ == "__main__":
    print("=" * 70)
    print("SYMBOLIC: which D-intervals collapse to EMPTY as k decreases?")
    print("=" * 70)
    for k in (7, 6, 5, 4):
        for m in (2, 3):
            symbolic_report(k, m)
        print()
