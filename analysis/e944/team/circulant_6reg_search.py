#!/usr/bin/env python3
"""
circulant_6reg_search.py — search 6-REGULAR circulants C_n(S), |S|=3, for an
E944 / (4,1)-graph witness, under Skottova-Steiner Prop 5.1 necessary conditions
(min-deg>=6, |V|>=11). This is the focused test of Steiner's "circulant (4,1)
probably don't exist" lean over ARBITRARY distance sets (not just his D1 family).
(count, E944)

A 6-regular circulant: S = {a,b,c} with a<b<c, c < n/2 (so each generates 2
neighbors; if c==n/2 it generates 1, breaking 6-regularity), gcd(S∪{n})=1.
Conditions to be a witness:
  chi == 4, vertex-critical (check vertex 0 by transitivity), and ALL THREE
  difference-orbits non-critical (0 critical edges).

We ALSO run the min-deg>=6 non-regular case (|S| in {3,4,5} incl. the n/2 half-
difference) to be thorough, but 6-regular is Steiner's Problem 5.2 target.
"""
import itertools
from math import gcd
from critedge import chromatic_number
import networkx as nx


def circulant(n, S):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for d in S:
        for i in range(n):
            G.add_edge(i, (i + d) % n)
    return G


def is_connected_set(n, S):
    g = n
    for d in S:
        g = gcd(g, d)
    return g == 1


def witness_analysis(n, S):
    """Return None unless chi==4 & vertex-critical; else dict with critical diffs."""
    G = circulant(n, list(S))
    # degree check
    chi = chromatic_number(G)
    if chi != 4:
        return None
    H = G.copy(); H.remove_node(0)
    if chromatic_number(H) >= 4:
        return None  # not vertex-critical
    crit = []
    for d in S:
        e = (0, d % n)
        if not G.has_edge(*e):
            continue
        He = G.copy(); He.remove_edge(*e)
        if chromatic_number(He) < 4:
            crit.append(d)
    return {"n": n, "S": tuple(S), "m": G.number_of_edges(),
            "degree": dict(G.degree())[0],
            "critical_differences": crit, "num_crit_orbits": len(crit)}


def main(nmin=11, nmax=40, mode="6reg"):
    print(f"Circulant (4,1)-witness search, mode={mode}, n={nmin}..{nmax}")
    print("Prop 5.1 (Skottova-Steiner): witness needs min-deg>=6, |V|>=11.")
    print("Testing whether ANY distance set yields a circulant (4,1)-graph.\n")
    examined = 0
    best = None
    witnesses = []
    four_vc = 0
    for n in range(max(nmin, 11), nmax + 1):
        half = n // 2
        diffs = list(range(1, half + 1))
        if mode == "6reg":
            # 6-regular: choose 3 distinct differences all < n/2 (strictly), so
            # no half-difference (which would give degree 5 from that gen).
            usable = [d for d in diffs if 2 * d != n]  # exclude exact half
            size_choices = [3]
            pools = {3: usable}
        else:
            usable = diffs
            size_choices = [3, 4]
            pools = {s: usable for s in size_choices}
        for ssize in size_choices:
            for S in itertools.combinations(pools[ssize], ssize):
                if not is_connected_set(n, S):
                    continue
                res = witness_analysis(n, S)
                if res is None:
                    continue
                four_vc += 1
                examined += 1
                nc = res["num_crit_orbits"]
                if best is None or nc < best["num_crit_orbits"]:
                    best = res
                if nc == 0:
                    witnesses.append(res)
                    print(f"  *** WITNESS C_{n}({S}) deg={res['degree']} "
                          f"m={res['m']} ZERO critical edges ***")
        # progress line per n
        bs = (f"best so far C_{best['n']}({best['S']}) "
              f"{best['num_crit_orbits']}/{len(best['S'])} crit-orbits "
              f"deg={best['degree']}") if best else "no 4-vtx-critical circulant yet"
        print(f"  n={n}: 4-vtx-critical circulants cumul={four_vc}; {bs}")
    print("\n" + "=" * 64)
    print(f"4-vertex-critical circulants meeting deg>=6 examined: {four_vc}")
    if witnesses:
        print(f"WITNESSES: {len(witnesses)}")
        for w in witnesses:
            print(f"   C_{w['n']}({w['S']}) deg={w['degree']} m={w['m']}")
    else:
        print(f"NO circulant (4,1)-witness for n in {nmin}..{nmax}, mode={mode}.")
        if best:
            print(f"Closest: C_{best['n']}({best['S']}) deg={best['degree']} "
                  f"with {best['num_crit_orbits']}/{len(best['S'])} critical "
                  f"edge-orbits.")
        print("=> Corroborates Steiner's lean that circulant (4,1)-graphs likely")
        print("   don't exist (now tested over ARBITRARY 3-element distance sets,")
        print("   not just his D1={1..2m-1} family).")
    print("=" * 64)


if __name__ == "__main__":
    import sys
    nmin = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    mode = sys.argv[3] if len(sys.argv) > 3 else "6reg"
    main(nmin, nmax, mode)
