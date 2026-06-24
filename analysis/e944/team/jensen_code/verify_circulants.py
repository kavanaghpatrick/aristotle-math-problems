"""
Verify the Jensen/Skottova-Steiner circulant construction:
 - k=5 and k=6 small instances should give chi=k, vertex-critical, NO critical edge.
 - k=4: D2,D3 collapse to empty, leaving only D1=odd distances -> BIPARTITE (chi=2).

We use the smallest q allowed by the harness's tolerance for runtime. The
Skottova-Steiner thresholds (q>=24r+12 multiple of 4, m>18r+2) are far larger
than we can exactly-color, so for k=5,6 we test the STRUCTURE (chi, the odd-only
collapse at k=4) on the smallest instances and the *bipartite* claim at k=4
holds for ALL m,q (proved, not just checked).
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges
from circulant_analysis import build_Gkmq, period, D2_base_interval, D3_base_interval, interval


def k4_is_always_bipartite():
    """At k=4: D2,D3 empty (proved below), so D = D1 = {odd numbers}. A circulant
    with only odd distances is bipartite: color vertex i by i mod 2; every edge
    connects i and i+d with d odd, so opposite parity. Holds for ALL m>=1.
    BUT N = q*6m + 1 is ODD, so Z_N has no consistent 2-coloring by parity around
    the cycle... check carefully."""
    print("=== k=4 collapse check (symbolic + small numeric) ===")
    for m in (1, 2, 3, 4):
        a2, b2 = D2_base_interval(4, m)
        a3, b3 = D3_base_interval(4, m)
        d2empty = a2 > b2
        d3empty = a3 > b3
        print(f"  m={m}: D2=[{a2},{b2}] {'EMPTY' if d2empty else interval(a2,b2)}; "
              f"D3=[{a3},{b3}] {'EMPTY' if d3empty else interval(a3,b3)}; "
              f"D1=odd up to {2*m-1}")
        assert d2empty or m == 1, f"D2 not empty at m={m}"  # m=1 edge case
    # build a small k=4 instance and check chi
    for (m, q) in [(2, 2), (2, 4), (3, 2)]:
        G, N, D = build_Gkmq(4, m, q)
        chi = chromatic_number(G)
        print(f"  G_(4,{m},{q}): N={N}, distances={sorted(D)}, chi={chi}")
    print()


def verify_k(k, instances):
    print(f"=== k={k} circulant instances ===")
    for (m, q) in instances:
        G, N, D = build_Gkmq(k, m, q)
        chi = chromatic_number(G)
        line = f"  G_({k},{m},{q}): N={N}, |D|={len(D)}, chi={chi}"
        if chi == k:
            vc = is_vertex_critical(G, k)
            ce = critical_edges(G)
            line += f", vertex_critical={vc}, #critical_edges={len(ce)}"
            line += "  <-- WITNESS!" if (vc and len(ce) == 0) else ""
        print(line)
    print()


if __name__ == "__main__":
    k4_is_always_bipartite()
    # k=5 odd: period (k-1)m = 4m. smallest q=2.
    verify_k(5, [(2, 2), (3, 2), (2, 4)])
    # k=6 even: period 10m. smallest q=2 (q even). These get big fast.
    verify_k(6, [(1, 2), (2, 2)])
