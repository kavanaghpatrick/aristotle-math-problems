#!/usr/bin/env python3
"""
algebra_qcirc_v2.py — quasigroup-circulant v2, targeting the Prop 5.1 witness band.

v1 finding: QC graphs with |S|<=4 never reach 4-vertex-criticality at n>=11 (too sparse /
wrong degree). v2 forces the min-degree-6 regime (Skottova-Steiner Prop 5.1: any (4,1)-graph
has min degree >= 6, |V| >= 11, sparsest 6-regular) by:
  - larger generator sets |S| in {5,6,7,8} at n in {11,12,13,14},
  - SAT chi (faster than backtracking at this density), cross-checked by backtracking on any hit,
  - a local DE-CRITICALIZATION descent from the lowest-critical-edge candidates: greedily flip
    edges to reduce #critical edges while preserving (chi=4, vertex-critical).

Score = #critical edges; 0 on a 4-vertex-critical graph = (4,1)-WITNESS (dual-verified).
"""
import sys, os, random, itertools
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as H
import algebra_substrate as A
import algebra_quasigroup as Q
import algebra_qcirculant as QC


def chi_sat(e, n):
    return H.chromatic_number_sat(e, n)


def vertex_critical_sat(e, n, k=4):
    if chi_sat(e, n) != k:
        return False
    adj = H.edges_to_adj(e, n)
    for v in range(n):
        sub_adj, sub_n = H.adj_remove_vertex(adj, n, v)
        sub_e = []
        for a in range(sub_n):
            nb = sub_adj[a]
            while nb:
                low = nb & (-nb); b = low.bit_length() - 1
                if a < b: sub_e.append((a, b))
                nb ^= low
        if chi_sat(sub_e, sub_n) >= k:
            return False
    return True


def n_critical_edges_sat(e, n, k=4):
    return sum(1 for ed in e if chi_sat(H.edges_remove_edge(e, ed), n) < k)


def descend(e, n, k=4, rounds=40, rng=None):
    """Local de-criticalization: try ADDING an edge (reduces criticality by adding redundancy)
    while preserving chi=4 and vertex-criticality; greedily reduce #critical edges."""
    rng = rng or random.Random(0)
    cur = set(map(lambda t: (min(t), max(t)), e))
    best_crit = n_critical_edges_sat(list(cur), n, k)
    all_pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    improved = True
    rounds_done = 0
    while improved and rounds_done < rounds and best_crit > 0:
        improved = False
        rounds_done += 1
        rng.shuffle(all_pairs)
        for (i, j) in all_pairs:
            trial = set(cur)
            if (i, j) in trial:
                # removing rarely helps reduce criticality; skip
                continue
            trial.add((i, j))
            te = list(trial)
            if chi_sat(te, n) != k:
                continue
            if not vertex_critical_sat(te, n, k):
                continue
            c = n_critical_edges_sat(te, n, k)
            if c < best_crit:
                cur = trial; best_crit = c; improved = True
                break
    return list(cur), best_crit


if __name__ == "__main__":
    print("=== quasigroup-circulant v2 (Prop 5.1 band, SAT chi) ===\n")
    builders = {"QC-left": QC.qcirc_left, "QC-diff": QC.qcirc_diff}
    overall_best = None
    for n in (11, 12, 13, 14):
        best = None
        tested = 0; n4vc = 0
        for sd in range(25):
            L = Q.random_latin_square(n, seed=sd)
            if L is None:
                continue
            for size in (5, 6, 7, 8):
                for S in itertools.combinations(range(n), size):
                    for bname, build in builders.items():
                        G = build(L, list(S))
                        e, nn = A.nx_to_edges_n(G)
                        if nn != n:
                            continue
                        # quick min-degree gate
                        deg = [0] * nn
                        for u, v in e:
                            deg[u] += 1; deg[v] += 1
                        if min(deg) < 6:
                            continue
                        tested += 1
                        if chi_sat(e, nn) != 4:
                            continue
                        if not vertex_critical_sat(e, nn, 4):
                            continue
                        n4vc += 1
                        ncrit = n_critical_edges_sat(e, nn, 4)
                        if best is None or ncrit < best[0]:
                            best = (ncrit, bname, S, e, nn)
                        if ncrit == 0:
                            # DUAL VERIFY with backtracking
                            assert H.chi_bt(e, nn) == 4 and H.is_vertex_critical(e, nn, 4) \
                                   and H.has_no_critical_edge(e, nn, 4)
                            print(f"  <<< WITNESS n={n} {bname} S={S} (dual-verified) >>>")
            # cap work per n
            if tested > 4000:
                break
        msg = f"n={n}: tested(min-deg>=6)={tested} 4-vertex-critical={n4vc}"
        if best:
            msg += f" best #crit_edges={best[0]} ({best[1]} S={best[2]})"
            if overall_best is None or best[0] < overall_best[0]:
                overall_best = (best[0], n, best[1], best[2], best[3], best[4])
        print(msg)

    if overall_best and overall_best[0] > 0:
        print(f"\nDescent from overall best (#crit={overall_best[0]}, n={overall_best[1]})...")
        e, n = overall_best[4], overall_best[5]
        rng = random.Random(7)
        e2, c2 = descend(e, n, rounds=30, rng=rng)
        print(f"  after descent: #critical_edges {overall_best[0]} -> {c2}")
        if c2 == 0:
            assert H.chi_bt(e2, n) == 4 and H.is_vertex_critical(e2, n, 4) and H.has_no_critical_edge(e2, n, 4)
            print("  <<< WITNESS via descent (dual-verified) >>>")
            print("  edges:", sorted(e2))
