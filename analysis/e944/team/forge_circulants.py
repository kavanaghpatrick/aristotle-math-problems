#!/usr/bin/env python3
"""
forge_circulants.py — systematic search over circulant graphs C_n(S).

MOTIVATION: complement(C7) = C7(2,3) is the unique n=7 4-vertex-critical graph
with the MAXIMUM redundant-edge fraction (50%). Circulants have a vertex-transitive
automorphism group (Z_n acts), so:
  - vertex-criticality is "all or nothing": if ONE vertex is critical, ALL are
    (by transitivity). Great — automatically vertex-critical if 4-chromatic and
    G-v is 3-colorable for one v.
  - edge-orbits under Z_n: edges of 'length' s form one orbit, so ALL edges of a
    given connection-length s are critical or all redundant TOGETHER.
So for a circulant, #critical-edge-orbits is what matters. If EVERY connection
length gives a redundant orbit, the circulant is a WITNESS.

This is the key structural lever: we only need to make each connection length's
edge redundant, and by symmetry that handles all n edges of that length at once.

We sweep C_n(S) for n up to ~40 and connection sets S, testing:
  chi == 4, vertex-critical (one vertex check), and critical-edge orbits.
"""
import itertools
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, is_e944_witness)


def circulant(n, S):
    """C_n(S): vertices Z_n, i~j iff (i-j mod n) in +-S."""
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for i in range(n):
        for s in S:
            G.add_edge(i, (i + s) % n)
    return G


def edge_length(u, v, n):
    d = (u - v) % n
    return min(d, n - d)


def circulant_profile(n, S, verbose=False):
    """Return dict: chi, vertex_critical, and per-length critical/redundant.
    Fast: tests chi==4 via 3-/4-colorability short-circuits, not full chi."""
    G = circulant(n, S)
    res = {"n": n, "S": tuple(sorted(S)), "m": G.number_of_edges()}
    # chi == 4 iff NOT 3-colorable AND 4-colorable
    if is_k_colorable(G, 3):
        res["chi"] = "<=3"; res["witness"] = False; return res
    if not is_k_colorable(G, 4):
        res["chi"] = ">=5"; res["witness"] = False; return res
    res["chi"] = 4
    # vertex-transitive: check criticality at ONE vertex only (vertex 0).
    H0 = G.copy(); H0.remove_node(0)
    vc = is_k_colorable(H0, 3)  # G-0 3-colorable => vertex 0 critical => all critical
    res["vertex_critical"] = vc
    if not vc:
        res["witness"] = False
        return res
    # per connection-length criticality (one representative edge per length).
    # By Z_n edge-transitivity within a length-orbit, one rep settles the orbit.
    crit_lengths = []
    red_lengths = []
    for s in sorted(S):
        L = s if s <= n - s else n - s
        H = G.copy()
        if H.has_edge(0, s % n):
            H.remove_edge(0, s % n)
            # edge critical iff G-e becomes 3-colorable
            if is_k_colorable(H, 3):
                crit_lengths.append(L)
            else:
                red_lengths.append(L)
    res["critical_lengths"] = crit_lengths
    res["redundant_lengths"] = red_lengths
    res["witness"] = (len(crit_lengths) == 0)
    return res


def sweep_circulants(nmax=40):
    print("Sweeping circulants C_n(S), n<=%d, |S| in {2,3,4} ..." % nmax)
    best = None  # (num_critical_lengths, n, S)
    witnesses = []
    for n in range(7, nmax + 1):
        maxs = n // 2
        cands = list(range(1, maxs + 1))
        for size in (2, 3, 4, 5):
            for S in itertools.combinations(cands, size):
                # must be connected & 4-regular-ish; quick degree sanity
                G = circulant(n, set(S))
                if min(dict(G.degree()).values()) < 3:
                    continue
                if not nx.is_connected(G):
                    continue
                p = circulant_profile(n, set(S))
                if p["chi"] != 4 or not p.get("vertex_critical"):
                    continue
                ncrit = len(p["critical_lengths"])
                # log EVERY 4-vertex-critical circulant with <=1 critical length
                if ncrit <= 1:
                    print(f"  C_{n}{tuple(sorted(S))}: chi=4 vc=True "
                          f"critical_lengths={p['critical_lengths']} "
                          f"redundant_lengths={p['redundant_lengths']} "
                          f"(m={p['m']}) ncrit={ncrit}", flush=True)
                if best is None or ncrit < best[0]:
                    best = (ncrit, n, tuple(sorted(S)))
                if p["witness"]:
                    print(f"  *** WITNESS: C_{n}({tuple(sorted(S))}) ***")
                    witnesses.append((n, tuple(sorted(S))))
    return best, witnesses


if __name__ == "__main__":
    # Sanity: C7(2,3) should be 50% redundant.
    print("=== C7(2,3) [= complement(C7)] ===")
    print(circulant_profile(7, {2, 3}))
    print()
    best, witnesses = sweep_circulants(nmax=40)
    print(f"\nBest (fewest critical edge-lengths): {best}")
    if witnesses:
        print(f"WITNESSES FOUND: {witnesses}")
    else:
        print("No circulant witness found up to n=40 with |S|<=4.")
