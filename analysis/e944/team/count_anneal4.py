#!/usr/bin/env python3
"""
count_anneal4.py — Prop-5.1-CONSTRAINED assault annealer (count, E944).

KEY FIX over anneal1-3: the previous chains reached 9-10 critical edges but did so
by DROPPING below min-degree 6 — those graphs can NEVER be witnesses (Prop 5.1:
witness needs min-deg >= 6, edge-connectivity >= 6, n >= 11). My E* fragmentation
study found the score-9 graph had degree sequence with min-deg 4. So the scorer
was rewarding infeasible escapes.

This scorer ADDS a hard-ish penalty for min-degree < 6 (and a soft nudge for
max-degree > n-5, the other Prop 5.1 bound), keeping the search inside the FEASIBLE
witness region while still minimizing critical edges. Targeted de-criticalization
move reused. n=12..18.

A score-0 here is a genuine Prop-5.1-compliant (4,1)-witness candidate.
"""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, random_move, undo_move, seed_random_regular, chi_exact
from count_anneal3 import targeted_move
import networkx as nx

W_CHI = 50.0
W_VC = 10.0
W_DEG = 6.0   # penalty per unit of min-degree deficit below 6
W_MAXDEG = 2.0


def score4(g, want_chi=4):
    n = g.n
    degs = [g.degree(v) for v in range(n)]
    mindeg = min(degs); maxdeg = max(degs)
    deg_pen = 0.0
    if mindeg < 6:
        deg_pen += W_DEG * (6 - mindeg) * 2  # strong push to >=6
    if maxdeg > n - 5:
        deg_pen += W_MAXDEG * (maxdeg - (n - 5))
    c = g.chi()
    chi_pen = 0.0
    if c != want_chi:
        chi_pen = W_CHI * (abs(c - want_chi) + (5 if c < want_chi else 0))
    noncrit_v = 0
    if c == want_chi:
        for v in range(n):
            if g.chi_minus_vertex(v) >= want_chi:
                noncrit_v += 1
    else:
        noncrit_v = n
    crit_e = 0
    if c == want_chi:
        for (a, b) in g.edges:
            if g.chi_minus_edge(a, b) < want_chi:
                crit_e += 1
    total = chi_pen + W_VC * noncrit_v + deg_pen + 1.0 * crit_e
    return total, (c, noncrit_v, crit_e, mindeg, maxdeg)


def mixed_move(g, rng, p_targeted=0.35):
    if rng.random() < p_targeted:
        mv = targeted_move(g, rng)
        if mv[0] != "noop":
            return mv
    return random_move(g, rng)


def anneal4(g0, rng, iters, T0=5.0, Tend=0.02, tag="", report_every=25000):
    g = g0.copy()
    cur, cur_info = score4(g)
    best = cur; best_g = g.copy(); best_info = cur_info
    decay = (Tend/T0) ** (1.0/max(1, iters))
    T = T0; t0 = time.time()
    for it in range(iters):
        mv = mixed_move(g, rng)
        if mv[0] == "noop":
            T *= decay; continue
        new, new_info = score4(g)
        d = new - cur
        if d <= 0 or rng.random() < math.exp(-d / max(T, 1e-9)):
            cur, cur_info = new, new_info
            if new < best:
                best = new; best_g = g.copy(); best_info = new_info
                # witness = chi 4, 0 noncritV, 0 critE, mindeg>=6
                if best_info[0] == 4 and best_info[1] == 0 and best_info[2] == 0 \
                   and best_info[3] >= 6:
                    return best, best_g, best_info, it
        else:
            undo_move(g, mv)
        T *= decay
        if report_every and it % report_every == 0 and it > 0:
            print(f"  [{tag}] it={it} T={T:.2f} cur={cur:.1f} best={best:.1f} "
                  f"info(chi,ncV,crE,minD,maxD)={best_info} ({time.time()-t0:.0f}s)",
                  flush=True)
    return best, best_g, best_info, -1


def main():
    rng = random.Random(60606)
    print("=== count ASSAULT annealer 4: Prop-5.1-CONSTRAINED (min-deg>=6) ===")
    print("scorer adds min-deg-6 penalty so search stays in FEASIBLE witness region\n")
    runs = []
    # seed from 6-regular (already min-deg 6) at the live n
    for n in (12, 13, 14, 15, 16, 17, 18):
        gs = seed_random_regular(n, 6, rng)
        if gs: runs.append((f"6reg-n{n}", gs, 100000))
    overall = None; hits = []
    for tag, gs, iters in runs:
        print(f"--- {tag} (n={gs.n}, m={len(gs.edges)}), {iters} iters")
        b, bg, binfo, hit = anneal4(gs, rng, iters, tag=tag)
        print(f"  => {tag}: best={b:.1f} info(chi,ncV,crE,minD,maxD)={binfo}", flush=True)
        if hit >= 0:
            hits.append((tag, sorted(bg.edges), bg.n))
            print(f"  *** WITNESS CANDIDATE {tag} edges={sorted(bg.edges)} ***", flush=True)
        if overall is None or b < overall[0]:
            overall = (b, tag, binfo, sorted(bg.edges), bg.n)
    print("\n" + "="*60)
    if hits:
        print(f"WITNESS CANDIDATES {len(hits)} — DUAL-VERIFY IMMEDIATELY")
        for t, e, n in hits: print(f"  {t} n={n} edges={e}")
    print(f"OVERALL BEST score={overall[0]:.1f} from {overall[1]} info={overall[2]} n={overall[4]}")
    print(f"edges={overall[3]}")
    print("="*60)


if __name__ == "__main__":
    main()
