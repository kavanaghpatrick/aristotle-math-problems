"""
INTERPOLATION LADDER — minimum critical-edge count over 4-vertex-critical graphs (proximity).

team-lead's assault question: at n=13..16, what is the MINIMUM number of critical edges achievable
by a 4-vertex-critical graph satisfying the Prop-5.1 necessary conditions?
  - minimum == 0  ⟹  that graph IS a (4,1)-graph = WITNESS to E944 k=4.
  - minimum provably floors at > 0 for a regime  ⟹  impossibility intel for that regime.

This complements count's simulated-annealing annealer (heuristic, finds low-but-maybe-not-min) with
an EXACT structural search: we enumerate structurally-feasible 4-vertex-critical graphs via the
constraint-engineered SAT model (proximity_witness_sat) and track the exact minimum critical-edge
count seen. Within a bounded candidate budget this gives an UPPER bound on the true minimum (and, if
the structural model is exhausted, the EXACT minimum over the constrained class).

critical-edge count of G = #edges e such that chi(G - e) < 4  (uses shared checkers, chi cross-checked).

We sweep edge-count windows (6-regular = 3n edges is the sparsest by Prop 5.1; denser graphs allowed
up to the max-degree bound). We start at the sparse end where witnesses are most plausible.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as C
import proximity_witness_sat as P


def critical_edge_count(edges, n):
    """Number of edges e with chi(G - e) < 4 (i.e. critical). For a 4-vertex-critical G."""
    c = 0
    for e in edges:
        if C.chi_bt(C.edges_remove_edge(edges, e), n) < 4:
            c += 1
    return c


def ladder_min_critical(n, edge_lo, edge_hi, max_candidates=20000, k4_free=True,
                        report_every=300, time_budget_s=600):
    """Over structurally-feasible 4-vertex-critical graphs on n vertices with edge count in
    [edge_lo, edge_hi], find the minimum critical-edge count. Returns (min_count, best_edges, stats)."""
    gm = P.GraphModel(n)
    P.apply_structural_constraints(gm, k4_free=k4_free, edge_lo=edge_lo, edge_hi=edge_hi)
    t0 = time.time()
    tested = 0
    vc_graphs = 0
    best = (10**9, None)
    while tested < max_candidates and time.time() - t0 < time_budget_s:
        edges = gm.solve_next()
        if edges is None:
            return best[0], best[1], dict(tested=tested, vc_graphs=vc_graphs, exhausted=True,
                                          secs=round(time.time()-t0, 1))
        tested += 1
        if not P.lambda_at_least_6(edges, n):
            gm.block_solution(set(edges)); continue
        if C.chi_bt(edges, n) != 4:
            gm.block_solution(set(edges)); continue
        if not C.is_vertex_critical(edges, n, 4):
            gm.block_solution(set(edges)); continue
        vc_graphs += 1
        cc = critical_edge_count(edges, n)
        if cc < best[0]:
            best = (cc, list(edges))
            print(f"  n={n}: NEW MIN critical-edge count = {cc} "
                  f"(|E|={len(edges)}, after {tested} cands)")
            if cc == 0:
                # dual-verify witness with SAT chi before alerting
                if C.chromatic_number_sat(edges, n) == 4 and C.has_no_critical_edge(edges, n, 4):
                    print(f"  *** WITNESS (0 critical edges) at n={n}! edges={edges} ***")
                    return 0, list(edges), dict(tested=tested, vc_graphs=vc_graphs, witness=True,
                                                secs=round(time.time()-t0, 1))
        gm.block_solution(set(edges))
        if report_every and tested % report_every == 0:
            print(f"  ...n={n}: {tested} cands, {vc_graphs} 4-vertex-critical, "
                  f"current min crit-edges = {best[0]}, {time.time()-t0:.0f}s")
    return best[0], best[1], dict(tested=tested, vc_graphs=vc_graphs,
                                  hit_limit=True, secs=round(time.time()-t0, 1))


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    # sparse window first: 6-regular = 3n edges; allow a small band above it
    base = 3 * n
    elo = int(sys.argv[2]) if len(sys.argv) > 2 else base
    ehi = int(sys.argv[3]) if len(sys.argv) > 3 else base + 2
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 8000
    print(f"=== Interpolation ladder: min critical-edge count, n={n}, |E| in [{elo},{ehi}] ===")
    m, best, stats = ladder_min_critical(n, elo, ehi, max_candidates=cap)
    print(f"\nRESULT n={n}: minimum critical-edge count found = {m}")
    print(f"stats: {stats}")
    if m == 0:
        print("  *** ZERO critical edges = (4,1)-GRAPH WITNESS ***")
    elif best:
        print(f"  best graph |E|={len(best)} has {m} critical edges")
