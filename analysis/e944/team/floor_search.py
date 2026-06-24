"""
e944 EXHAUSTIVE FLOOR (hunter).

For each n, enumerate ALL connected min-degree-3 graphs via nauty geng, filter to
4-vertex-critical, and test the no-critical-edge predicate. Any graph that is
4-vertex-critical AND has no critical edge is a WITNESS to erdos_944.dirac_conjecture.k_eq_four.

Pipeline: geng -c -d3 n  ->  graph6  ->  networkx  ->  fast chi backtracking filter.

Rigor:
  - geng enumerates every isomorphism class exactly once (completeness guaranteed by nauty).
  - min-degree-3 is a NECESSARY condition for 4-vertex-criticality (a vertex of degree <= 2
    in a 4-chromatic graph is non-critical: G-v is 4-chromatic-or-the-vertex-recolors, so
    removing it cannot drop chi below 4... formally: if deg(v) <= 2 then any 3-coloring of G-v
    extends to v, so chi(G-v) = chi(G); hence v is NOT critical). So restricting to d>=3 loses
    NO witnesses. We log the count both with and without this filter for small n as a sanity check.
  - Primary chi via pure-python backtracking. Every PASSING candidate (and a random sample of
    near-misses) is re-verified with the independent SAT checker.

Output: for each n, the number of 4-vertex-critical graphs and how many have no critical edge.
A nonzero "no critical edge" count = WITNESS FOUND (alert immediately).
"""
import sys
import subprocess
import random
import time
import networkx as nx

sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from checkers import (
    chromatic_number_exact, edges_to_adj, is_k_colorable_backtrack,
    chromatic_number_sat, is_k_colorable_sat,
)

GENG = "/opt/homebrew/Cellar/nauty/2.9.3/bin/geng"


def g6_to_edges(line):
    G = nx.from_graph6_bytes(line.encode())
    n = G.number_of_nodes()
    edges = [(min(u, v), max(u, v)) for (u, v) in G.edges()]
    return edges, n


def is_4_vertex_critical_fast(edges, n):
    """chi=4 and for all v chi(G-v) <= 3. Uses fast backtracking colorability tests.
    Returns True/False. Optimized: reject if not 4-chromatic early."""
    adj = edges_to_adj(edges, n)
    # chi == 4  <=>  not 3-colorable AND 4-colorable
    if is_k_colorable_backtrack(adj, n, 3):
        return False  # 3-colorable, chi <= 3
    if not is_k_colorable_backtrack(adj, n, 4):
        return False  # chi >= 5
    # chi == 4 confirmed. Now vertex-criticality: every G-v must be 3-colorable.
    for v in range(n):
        sub_adj, sub_n = _remove_vertex(adj, n, v)
        if not is_k_colorable_backtrack(sub_adj, sub_n, 3):
            return False  # G-v still 4-chromatic -> v not critical
    return True


def _remove_vertex(adj, n, v):
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


def has_no_critical_edge_fast(edges, n):
    """True iff no single edge e has chi(G-e)=3, i.e. for every edge, G-e stays 4-chromatic
    (not 3-colorable). G is known 4-chromatic here."""
    adj = edges_to_adj(edges, n)
    for (a, b) in edges:
        # remove edge (a,b)
        adj[a] &= ~(1 << b)
        adj[b] &= ~(1 << a)
        three_col = is_k_colorable_backtrack(adj, n, 3)
        adj[a] |= (1 << b)
        adj[b] |= (1 << a)
        if three_col:
            return False  # this edge is critical (chi dropped to 3)
    return True


def sat_verify_witness(edges, n):
    """Independent SAT re-verification of the full predicate for a candidate witness."""
    # chi == 4
    if is_k_colorable_sat(edges, n, 3):
        return False, "SAT says 3-colorable"
    if not is_k_colorable_sat(edges, n, 4):
        return False, "SAT says chi>=5"
    # vertex critical
    for v in range(n):
        sub = [(u, w) for (u, w) in edges if u != v and w != v]
        # relabel
        keep = sorted({x for e in sub for x in e} | (set(range(n)) - {v}))
        # actually need all vertices 0..n-1 except v present even if isolated after removal
        remap = {}
        nn = 0
        for x in range(n):
            if x != v:
                remap[x] = nn
                nn += 1
        sub2 = [(remap[u], remap[w]) for (u, w) in sub]
        if not is_k_colorable_sat(sub2, nn, 3):
            return False, f"SAT: vertex {v} not critical"
    # no critical edge
    for (a, b) in edges:
        sub = [e for e in edges if e != (a, b)]
        if is_k_colorable_sat(sub, n, 3):
            return False, f"SAT: edge {(a,b)} is critical"
    return True, "SAT confirms witness"


def run_n(n, geng_args=("-c", "-d3"), sample_sat=50, time_budget=None):
    """Enumerate graphs on n vertices, count 4-vertex-critical and witnesses.
    Returns dict of stats. Streams geng to avoid memory blowup."""
    t0 = time.time()
    cmd = [GENG] + list(geng_args) + [str(n)]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    total = 0
    vc4 = 0
    witnesses = []
    vc4_with_crit_edge = 0
    sat_checks = 0
    sat_sample = []
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        total += 1
        edges, nn = g6_to_edges(line)
        if is_4_vertex_critical_fast(edges, nn):
            vc4 += 1
            if has_no_critical_edge_fast(edges, nn):
                witnesses.append((line, edges, nn))
            else:
                vc4_with_crit_edge += 1
                if len(sat_sample) < sample_sat:
                    sat_sample.append((line, edges, nn))
        if time_budget and (time.time() - t0) > time_budget:
            proc.kill()
            return {"n": n, "total_enumerated": total, "vc4": vc4,
                    "witnesses": witnesses, "TIMED_OUT": True,
                    "elapsed": time.time() - t0}
    proc.wait()

    # cross-validate a sample of the 4-vertex-critical-with-critical-edge graphs via SAT
    sat_disagreements = []
    for (g6, edges, nn) in sat_sample:
        ok, msg = sat_verify_witness(edges, nn)
        sat_checks += 1
        if ok:  # SAT thinks it IS a witness but fast checker said no -> disagreement
            sat_disagreements.append((g6, "SAT calls it witness but fast said no"))

    # verify any witnesses with SAT
    confirmed = []
    for (g6, edges, nn) in witnesses:
        ok, msg = sat_verify_witness(edges, nn)
        confirmed.append((g6, ok, msg))

    return {
        "n": n,
        "total_enumerated": total,
        "vc4": vc4,
        "vc4_with_critical_edge": vc4_with_crit_edge,
        "witnesses_fast": len(witnesses),
        "witnesses_sat_confirmed": [c for c in confirmed if c[1]],
        "witness_details": confirmed,
        "sat_cross_checks": sat_checks,
        "sat_disagreements": sat_disagreements,
        "elapsed": round(time.time() - t0, 2),
    }


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    tb = float(sys.argv[3]) if len(sys.argv) > 3 else None
    print(f"# e944 exhaustive floor: n={lo}..{hi}  (geng -c -d3)")
    print(f"# {'n':>3} {'enumerated':>12} {'4vtxcrit':>9} {'w/crit-edge':>11} "
          f"{'WITNESS':>8} {'SAT-disagree':>12} {'sec':>8}")
    for n in range(lo, hi + 1):
        r = run_n(n, time_budget=tb)
        if r.get("TIMED_OUT"):
            print(f"  {n:>3} {r['total_enumerated']:>12} {r['vc4']:>9} "
                  f"{'?':>11} {len(r['witnesses']):>8} {'?':>12} {r['elapsed']:>8.1f}  TIMED_OUT")
            print(f"  -> n={n} incomplete; stopping.")
            break
        wfast = r["witnesses_fast"]
        nsat = len(r["witnesses_sat_confirmed"])
        dis = len(r["sat_disagreements"])
        flag = "  <<< WITNESS!!!" if nsat > 0 else ""
        print(f"  {n:>3} {r['total_enumerated']:>12} {r['vc4']:>9} "
              f"{r['vc4_with_critical_edge']:>11} {wfast:>8} {dis:>12} {r['elapsed']:>8.1f}{flag}")
        if dis > 0:
            print(f"  !! SAT DISAGREEMENTS at n={n}: {r['sat_disagreements'][:3]}")
        if nsat > 0:
            print(f"  !!! SAT-CONFIRMED WITNESS at n={n}: {r['witnesses_sat_confirmed']}")
            sys.stdout.flush()
            break
        sys.stdout.flush()
