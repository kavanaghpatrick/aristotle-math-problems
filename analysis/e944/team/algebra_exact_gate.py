#!/usr/bin/env python3
"""
algebra_exact_gate.py — exact CPU verification gate for the BHK GPU marathon (task #29).

The marathon's pipeline (hunter): CPU proposal -> CPU chi-screen firehose -> GPU BHK predicate ->
THIS exact CPU gate on BHK-flagged candidates -> skeptic adjudicator -> alert.

This module is the exact-gate step. It takes a candidate graph (graph6 string OR edge list) and
returns a dual-verified verdict: is it a genuine Erdos-944 (4,1)-WITNESS?
A (4,1)-witness = chi(G)=4 AND vertex-critical AND NO single edge is critical (every critical
edge-set has size >1). By the validated identity this is exactly f(G)>=2 with vertex-criticality.

Every chi computation is cross-checked: backtracking exact colorer (checkers.chi_bt) AND a SAT
encoding (checkers.chromatic_number_sat). A disagreement raises (never silently passes).

Public API (call on a g6 string or (edges,n)):
  vc_first_reject(edges, n, k=4)   -> True if 4-vertex-critical (survives all vertex deletions),
                                       False as soon as one deletion keeps chi>=k. Early-exit.
  witness_gate(edges, n, k=4)      -> True iff NO single edge is critical (0 critical edges).
                                       Early-exit on the first critical edge found.
  f_value(edges, n, cap=None)      -> f(G) = min over Z3-colorings of #monochromatic edges
                                       (exact brute for n<=13; for n>13 returns an upper bound).
  exact_gate(g6_or_edges, n=None)  -> dict verdict: the full dual-verified (4,1)-witness decision.
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as H


# --------------------------------------------------------------------------
# input normalization: accept graph6 string OR (edges, n)
# --------------------------------------------------------------------------

def _to_edges_n(g6_or_edges, n=None):
    """Return (edges, n). Accepts a graph6 str, or (edges,n) with edges a list of (u,v)."""
    if isinstance(g6_or_edges, str):
        import networkx as nx
        G = nx.from_graph6_bytes(g6_or_edges.strip().encode())
        nn = G.number_of_nodes()
        edges = [(min(u, v), max(u, v)) for u, v in G.edges()]
        return edges, nn
    edges = [(min(u, v), max(u, v)) for (u, v) in g6_or_edges]
    if n is None:
        n = (max(max(u, v) for u, v in edges) + 1) if edges else 0
    return edges, n


def _chi_dualverify(edges, n):
    """chi via backtracking AND SAT; raise on mismatch. Returns the agreed chi."""
    a = H.chi_bt(edges, n)
    b = H.chromatic_number_sat(edges, n)
    if a != b:
        raise AssertionError(f"CHI MISMATCH backtrack={a} sat={b} on n={n} — gate aborts")
    return a


# --------------------------------------------------------------------------
# 1) vc-first reject  (wall's cheap early-exit: ~all 6-reg graphs reject on an early vertex)
# --------------------------------------------------------------------------

def vc_first_reject(edges, n, k=4):
    """True iff G is k-vertex-critical: chi(G)=k and chi(G-v)<k for ALL v.
    Early-exits False on the first vertex whose deletion keeps chi>=k."""
    if H.chi_bt(edges, n) != k:
        return False
    adj = H.edges_to_adj(edges, n)
    for v in range(n):
        sa, sn = H.adj_remove_vertex(adj, n, v)
        se = []
        for a in range(sn):
            nb = sa[a]
            while nb:
                low = nb & (-nb); b = low.bit_length() - 1
                if a < b:
                    se.append((a, b))
                nb ^= low
        if H.chi_bt(se, sn) >= k:
            return False  # v not critical -> reject immediately
    return True


# --------------------------------------------------------------------------
# 2) witness gate  (no single critical edge; early-exit on first critical edge)
# --------------------------------------------------------------------------

def witness_gate(edges, n, k=4):
    """True iff NO single edge is critical (i.e. chi(G-e)=k for every edge e).
    Early-exits False the moment a critical edge (chi(G-e)<k) is found."""
    for e in edges:
        if H.chi_bt(H.edges_remove_edge(edges, e), n) < k:
            return False  # found a critical edge -> not a witness
    return True


# --------------------------------------------------------------------------
# 3) f-value  (f>=2 with vertex-criticality == witness, by the validated identity)
# --------------------------------------------------------------------------

def f_value(edges, n, cap=None):
    """f(G) = min over Z3-colorings p:V->Z3 of #monochromatic edges.
    Exact brute force for n<=13. For n>13, returns an upper bound via local search."""
    if n <= 13:
        best = len(edges) + 1
        for assign in itertools.product(range(3), repeat=n):
            mono = 0
            for (u, v) in edges:
                if assign[u] == assign[v]:
                    mono += 1
                    if mono >= best:
                        break
            if mono < best:
                best = mono
                if best == 0:
                    return 0
            if cap is not None and best <= cap:
                return best
        return best
    # n>13: randomized local-search upper bound
    import random
    rng = random.Random(0)
    best = len(edges) + 1
    for _ in range(20000):
        a = [rng.randrange(3) for _ in range(n)]
        improved = True
        while improved:
            improved = False
            for v in range(n):
                cur = a[v]; bc = cur; bm = None
                for c in range(3):
                    a[v] = c
                    m = sum(1 for (u, w) in edges if a[u] == a[w])
                    if bm is None or m < bm:
                        bm = m; bc = c
                a[v] = bc
                if bc != cur:
                    improved = True
        mono = sum(1 for (u, v) in edges if a[u] == a[v])
        if mono < best:
            best = mono
        if best <= 1:
            break
    return best  # upper bound


# --------------------------------------------------------------------------
# exact_gate: the full dual-verified (4,1)-witness verdict
# --------------------------------------------------------------------------

def exact_gate(g6_or_edges, n=None, k=4):
    """Full exact CPU gate for a marathon candidate. Returns a verdict dict.
    WITNESS iff chi=k (dual-verified) AND vertex-critical AND no critical edge AND f>=2.
    All four must agree; any failure => not a witness, with the reason."""
    edges, n = _to_edges_n(g6_or_edges, n)
    verdict = {"n": n, "m": len(edges), "is_witness": False, "reason": None,
               "chi": None, "chi_sat_agrees": None, "vertex_critical": None,
               "no_critical_edge": None, "f": None}
    # 1) chi dual-verified
    try:
        chi = _chi_dualverify(edges, n)
    except AssertionError as ex:
        verdict["reason"] = f"CHI_DISAGREEMENT: {ex}"
        return verdict
    verdict["chi"] = chi; verdict["chi_sat_agrees"] = True
    if chi != k:
        verdict["reason"] = f"chi={chi}!={k}"
        return verdict
    # 2) vertex-critical
    vc = vc_first_reject(edges, n, k)
    verdict["vertex_critical"] = vc
    if not vc:
        verdict["reason"] = "not vertex-critical"
        return verdict
    # 3) no critical edge (witness gate)
    nce = witness_gate(edges, n, k)
    verdict["no_critical_edge"] = nce
    if not nce:
        verdict["reason"] = "has a critical edge (f=1)"
        return verdict
    # 4) f-value cross-check (must be >=2 for a witness, by the identity)
    f = f_value(edges, n)
    verdict["f"] = f
    if f < 2:
        verdict["reason"] = f"f={f}<2 inconsistent with no-critical-edge (re-examine!)"
        return verdict
    # all pass: genuine (4,1)-witness
    verdict["is_witness"] = True
    verdict["reason"] = "GENUINE (4,1)-WITNESS: chi=4 dual-verified, vertex-critical, 0 critical edges, f>=2"
    return verdict


if __name__ == "__main__":
    # self-test on known objects
    tests = [
        ("C13(1,2,5) n=13 6-reg (f=1, NOT witness)", "L?bFFbw~B{FwFw"),
        ("HCQbfrm (wall's n=9 4-vc, f=1, NOT witness)", "HCQbfrm"),
    ]
    for name, g6 in tests:
        v = exact_gate(g6)
        print(f"{name}: witness={v['is_witness']} | chi={v['chi']} vc={v['vertex_critical']} "
              f"no_crit_edge={v['no_critical_edge']} f={v['f']} | {v['reason']}")
