#!/usr/bin/env python3
"""
forge_extremal.py — STABILITY/EXTREMAL lane (with jensen): what does ALMOST-zero
|E*| force structurally in a 4-vertex-critical graph?

Seeded from the proven floor |E*| ≥ ⌈n/2⌉ (vertex-spanning ⟹ E* is an edge cover).
Questions:
  1. EXTREMAL FUNCTION f(n) = min |E*| over 4-vertex-critical graphs on n vertices.
     Does it hit the ⌈n/2⌉ floor, or is the true minimum higher?
  2. STRUCTURE of the minimizers (the |E*|-extremal graphs): degree sequence, and
     the STRUCTURE of E* itself (is it forced to be a near-perfect matching? a
     specific subgraph?).
  3. STABILITY: as |E*| → f(n), what is forced? (E.g. min |E*| ⟹ E* is a perfect
     matching ⟹ each vertex incident to EXACTLY one critical edge ⟹ the "almost
     witness" structure.)

This is genuine extremal graph theory — NOT the dead analytic lever, NOT construction.
A stability theorem ("almost-zero |E*| ⟹ G is close to [structure X], which then
provably has a critical edge") would be a real route to the impossibility proof:
if every near-extremal graph is forced toward a structure that can't reach |E*|=0,
that closes the gap between the ⌈n/2⌉ floor and 0.
"""
import itertools
import subprocess
import networkx as nx
from forge_verify import is_k_colorable, critical_edges

GENG = "/opt/homebrew/bin/geng"


def is4vc(G):
    if is_k_colorable(G, 3) or not is_k_colorable(G, 4):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def Estar_structure(G):
    """Return E* and its structural summary."""
    ce = critical_edges(G, 4)
    E = nx.Graph(); E.add_edges_from(ce)
    touched = set(E.nodes())
    n = G.number_of_nodes()
    # is E* a matching? (max degree 1 in E*)
    estar_maxdeg = max((d for _, d in E.degree()), default=0)
    is_matching = estar_maxdeg <= 1
    # is E* a perfect/near-perfect matching covering all vertices?
    spanning = (len(touched) == n)
    comps = nx.number_connected_components(E) if E.number_of_nodes() else 0
    return {
        "size": len(ce), "touched": len(touched), "spanning": spanning,
        "estar_maxdeg": estar_maxdeg, "is_matching": is_matching,
        "components": comps,
        "edges": sorted(tuple(sorted(e)) for e in ce),
    }


def extremal_scan(n):
    """Find min |E*| over all 4-vertex-critical graphs on n vertices + minimizer structure."""
    import math
    me = math.ceil((5 * n - 2) / 3)
    floor_cover = (n + 1) // 2  # |E*| >= ceil(n/2)
    proc = subprocess.Popen([GENG, "-c", "-d3", str(n), f"{me}:{n*(n-1)//2}"],
                            stdout=subprocess.PIPE, text=True, bufsize=1)
    best = None  # (size, G, struct)
    minimizers = []
    total = 0
    for g6 in proc.stdout:
        g6 = g6.strip()
        if not g6:
            continue
        G = nx.from_graph6_bytes(g6.encode())
        if not is4vc(G):
            continue
        total += 1
        s = Estar_structure(G)
        if best is None or s["size"] < best[0]:
            best = (s["size"], g6, s)
            minimizers = [(g6, s, sorted([d for _, d in G.degree()], reverse=True))]
        elif s["size"] == best[0]:
            minimizers.append((g6, s, sorted([d for _, d in G.degree()], reverse=True)))
    return {
        "n": n, "total_4vc": total, "floor_cover": floor_cover,
        "min_Estar": best[0] if best else None,
        "minimizers": minimizers,
    }


if __name__ == "__main__":
    import sys
    ns = [int(x) for x in sys.argv[1:]] or [7, 8, 9, 10]
    print("=== EXTREMAL: min |E*| over 4-vertex-critical graphs + minimizer structure ===", flush=True)
    print("(floor = ⌈n/2⌉ from vertex-spanning edge-cover bound)\n", flush=True)
    for n in ns:
        r = extremal_scan(n)
        print(f"n={n}: {r['total_4vc']} four-vertex-critical graphs; "
              f"floor ⌈n/2⌉={r['floor_cover']}; MIN |E*|={r['min_Estar']}", flush=True)
        # structure of minimizers
        for g6, s, degseq in r["minimizers"][:4]:
            print(f"   minimizer g6={g6}: |E*|={s['size']} E*-maxdeg={s['estar_maxdeg']} "
                  f"matching={s['is_matching']} spanning={s['spanning']} "
                  f"comps={s['components']} degseq={degseq[:6]}...", flush=True)
        # how far above the floor?
        if r["min_Estar"]:
            gap = r["min_Estar"] - r["floor_cover"]
            print(f"   GAP above floor: {gap} (min |E*| {r['min_Estar']} vs floor {r['floor_cover']})", flush=True)
        print(flush=True)
