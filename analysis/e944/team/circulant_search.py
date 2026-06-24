#!/usr/bin/env python3
"""
circulant_search.py — search circulant graphs C_n(S) for an E944 witness:
4-vertex-critical with ZERO critical edges. (count, E944)

Circulant C_n(S): vertices Z_n, i~j iff (i-j mod n) in ±S, S subset of {1..n//2}.
Vertex-transitive ⇒ criticality is constant on edge orbits (one orbit per
difference d in S), and vertex-criticality need only be checked at vertex 0.

We exploit this: an edge of difference d is critical iff chi(C_n(S) - {one
difference-d edge}) < chi. So #critical-edge-orbits is checked with |S| chi
calls, not m calls. A witness needs ALL |S| differences non-critical.

Exact chi from critedge.py (self-tested).
"""
import itertools
import networkx as nx
from critedge import chromatic_number, is_vertex_critical


def circulant(n, S):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for d in S:
        for i in range(n):
            G.add_edge(i, (i + d) % n)
    return G


def edge_of_difference(n, d):
    return (0, d % n)


def analyze_circulant(n, S):
    """Return dict with chi, vertex_critical, and per-difference criticality.
    Uses vertex-transitivity: edge-orbit = difference."""
    G = circulant(n, S)
    chi = chromatic_number(G)
    if chi != 4:
        return None
    # vertex-criticality: by transitivity check vertex 0 only, BUT verify the
    # graph is actually vertex-transitive on this orbit (circulants are vertex-
    # transitive, so checking vertex 0 suffices for ALL vertices).
    H = G.copy(); H.remove_node(0)
    if chromatic_number(H) >= chi:
        return None  # vertex 0 not critical ⇒ not vertex-critical
    # per-difference edge criticality
    crit_diffs = []
    for d in S:
        e = edge_of_difference(n, d)
        if not G.has_edge(*e):
            continue
        He = G.copy(); He.remove_edge(*e)
        if chromatic_number(He) < chi:
            crit_diffs.append(d)
    return {"n": n, "S": tuple(S), "chi": chi, "vertex_critical": True,
            "m": G.number_of_edges(),
            "critical_differences": crit_diffs,
            "num_critical_edge_orbits": len(crit_diffs)}


def main(max_n=22):
    print("Circulant witness search: C_n(S), seeking 4-vertex-critical with 0 critical edges")
    print(f"n up to {max_n}\n")
    best = None  # fewest critical edge orbits
    found_witness = []
    candidates_4vc = 0
    for n in range(4, max_n + 1):
        half = n // 2
        diffs = list(range(1, half + 1))
        # iterate over non-empty connection sets; require connectivity (gcd of S
        # with n... actually require the graph connected). Limit |S| to keep it
        # tractable: a 4-chromatic circulant is fairly dense; allow |S| up to 5.
        for ssize in range(2, min(half, 5) + 1):
            for S in itertools.combinations(diffs, ssize):
                # connectivity quick check: gcd(S ∪ {n}) == 1
                from math import gcd
                g = n
                for d in S:
                    g = gcd(g, d)
                if g != 1:
                    continue
                res = analyze_circulant(n, list(S))
                if res is None:
                    continue
                candidates_4vc += 1
                nc = res["num_critical_edge_orbits"]
                if best is None or nc < best["num_critical_edge_orbits"] or \
                   (nc == best["num_critical_edge_orbits"] and n < best["n"]):
                    best = res
                if nc == 0:
                    found_witness.append(res)
                    print(f"  *** WITNESS: C_{n}({S}) chi=4 vertex-critical, "
                          f"ZERO critical edges! m={res['m']} ***")
        if best:
            print(f"  n<= {n}: best so far C_{best['n']}({best['S']}) "
                  f"crit-edge-orbits={best['num_critical_edge_orbits']} "
                  f"(of |S|={len(best['S'])}), m={best['m']}")
    print("\n" + "=" * 60)
    print(f"4-vertex-critical circulants examined: {candidates_4vc}")
    if found_witness:
        print(f"WITNESSES FOUND: {len(found_witness)}")
        for w in found_witness:
            print(f"   C_{w['n']}({w['S']}), m={w['m']}")
    else:
        print("NO circulant witness up to n =", max_n)
        if best:
            print(f"Closest: C_{best['n']}({best['S']}) with "
                  f"{best['num_critical_edge_orbits']} critical edge-orbit(s) "
                  f"out of |S|={len(best['S'])} differences.")
    print("=" * 60)


if __name__ == "__main__":
    import sys
    mx = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    main(mx)
