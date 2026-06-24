#!/usr/bin/env python3
"""
algebra_qcirculant.py — quasigroup-circulant substrate (algebra ASSAULT).

The DISTINCTIVE algebraic lever: generalize the circulant Cay(Z_n, ±D) by
replacing the abelian group (Z_n,+) with a NON-ASSOCIATIVE quasigroup (Q,*) of
the same order. In a true circulant the rotation r:i->i+1 is an automorphism that
acts transitively on each distance class => edge criticality is orbit-uniform
(the orbit obstruction that kills the symmetric substrate). With a non-associative
quasigroup the analogous map is NOT a graph automorphism, so the symmetry that
forces orbit-uniform criticality is broken — edges land in small/singleton orbits
and "no single edge critical" becomes attainable in principle.

Two ways to build a graph from a quasigroup (Q,*) of order n with a "generator
multiset" S subset Q:
  (QC-left):  i ~ j  iff  exists s in S with i*s = j  or  j*s = i   (left translations)
  (QC-diff):  i ~ j  iff  the unique x with i*x=j (left division i\\j) lies in S,
              symmetrized.

We require the connection structure to be SYMMETRIC (undirected) and to avoid
self-loops, then scan for the (4,1) property with hunter's verified checkers.

Score = #critical edges over 4-vertex-critical graphs; 0 => witness.
"""
import sys, os, random, itertools
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as H
import algebra_substrate as A
import algebra_quasigroup as Q


def left_div_table(L):
    """left division: ld[i][j] = unique x with L[i][x]=j  (i \\ j)."""
    n = len(L)
    ld = [[-1] * n for _ in range(n)]
    for i in range(n):
        for x in range(n):
            ld[i][L[i][x]] = x
    return ld


def qcirc_left(L, S):
    """QC-left: i~j iff exists s in S with L[i][s]=j (symmetrized)."""
    n = len(L)
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for i in range(n):
        for s in S:
            j = L[i][s]
            if j != i:
                G.add_edge(i, j)
    return G


def qcirc_diff(L, S):
    """QC-diff: i~j iff (i\\j) in S OR (j\\i) in S (symmetric by construction)."""
    n = len(L)
    ld = left_div_table(L)
    G = nx.Graph()
    G.add_nodes_from(range(n))
    Sset = set(S)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            if ld[i][j] in Sset or ld[j][i] in Sset:
                G.add_edge(i, j)
    return G


def scan_qcirculants(n, builders, max_squares=120, max_S=4, seed=0):
    """Scan random quasigroups of order n, all generator sets S up to size max_S,
    both builders, for a (4,1)-graph. Returns best (min critical edges) + witnesses."""
    rng = random.Random(seed)
    best = None
    witnesses = []
    tested = 0
    n4_vc = 0
    seeds = list(range(max_squares))
    for sd in seeds:
        L = Q.random_latin_square(n, seed=sd)
        if L is None:
            continue
        assoc = Q.is_associative(L)
        elems = list(range(n))
        for size in range(2, max_S + 1):
            for S in itertools.combinations(elems, size):
                for bname, build in builders.items():
                    G = build(L, S)
                    # enforce undirected simple; require min degree >= 1
                    e, nn = A.nx_to_edges_n(G)
                    if nn < 7:
                        continue
                    tested += 1
                    c = H.chi_bt(e, nn)
                    if c != 4:
                        continue
                    if not H.is_vertex_critical(e, nn, 4):
                        continue
                    n4_vc += 1
                    ncrit = sum(1 for ed in e if H.chi_bt(H.edges_remove_edge(e, ed), nn) < 4)
                    if best is None or ncrit < best[0]:
                        best = (ncrit, n, bname, S, assoc, nn, len(e))
                    if ncrit == 0:
                        witnesses.append((n, bname, S, assoc, L))
    return {"tested": tested, "n4_vertex_critical": n4_vc, "best": best,
            "witnesses": witnesses}


if __name__ == "__main__":
    print("=== quasigroup-circulant substrate scan (algebra ASSAULT) ===\n")
    builders = {"QC-left": qcirc_left, "QC-diff": qcirc_diff}
    for n in (8, 9, 11, 12, 13):
        res = scan_qcirculants(n, builders, max_squares=40, max_S=4, seed=n)
        b = res["best"]
        msg = (f"order n={n}: tested={res['tested']} "
               f"4-vertex-critical={res['n4_vertex_critical']} "
               f"witnesses={len(res['witnesses'])}")
        if b:
            msg += f"\n   best: #crit_edges={b[0]} builder={b[2]} S={b[3]} assoc={b[4]} V={b[5]} m={b[6]}"
        if res["witnesses"]:
            msg += f"\n   <<< WITNESS(ES): {[(w[0],w[1],w[2],w[3]) for w in res['witnesses'][:3]]} >>>"
        print(msg)
