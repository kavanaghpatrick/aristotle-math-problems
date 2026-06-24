#!/usr/bin/env python3
"""
count_anneal_mindeg6.py — min-degree>=6 CONSTRAINED annealer, IRREGULAR allowed.
(count, E944 ASSAULT)

Covers the feasible witness region that the strict-6-regular search excludes:
Prop 5.1 allows a witness to be IRREGULAR with min-deg >= 6 and max-deg <= n-5
(so m can exceed 3n). Move-set keeps min-deg >= 6 BY CONSTRUCTION:
  - edge ADD: always allowed (raises degrees).
  - edge DELETE: allowed only if BOTH endpoints stay >= 6 after removal.
  - 2-swap: degree-preserving, always degree-safe.
  - targeted de-criticalization: add-only (degree-safe).
Soft χ/vertex-crit penalties; score = #critical edges once feasible.

A score-0 here (chi=4, vertex-critical, min-deg>=6, no critical edge) is a genuine
Prop-5.1-compliant (4,1)-witness — DUAL-VERIFY and alert.
"""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, seed_random_regular, chi_exact
from count_anneal3 import three_coloring_of

W_CHI = 60.0
W_VC = 12.0
MIN_DEG = 6


def score_md(g, want_chi=4):
    c = g.chi()
    chi_pen = W_CHI*(abs(c-want_chi)+(5 if c<want_chi else 0)) if c != want_chi else 0.0
    noncrit_v = 0
    if c == want_chi:
        for v in range(g.n):
            if g.chi_minus_vertex(v) >= want_chi: noncrit_v += 1
    else:
        noncrit_v = g.n
    crit_e = 0
    if c == want_chi:
        for (a, b) in g.edges:
            if g.chi_minus_edge(a, b) < want_chi: crit_e += 1
    # max-degree soft penalty (Prop 5.1: Delta <= n-5)
    maxd = max(g.degree(v) for v in range(g.n))
    md_pen = 2.0*max(0, maxd-(g.n-5))
    return chi_pen + W_VC*noncrit_v + md_pen + 1.0*crit_e, (c, noncrit_v, crit_e,
            min(g.degree(v) for v in range(g.n)), maxd)


def safe_move(g, rng, p_targeted=0.35):
    n = g.n
    if rng.random() < p_targeted:
        mv = targeted_add(g, rng)
        if mv[0] != "noop": return mv
    r = rng.random()
    if r < 0.4:
        # add non-edge
        for _ in range(20):
            u, v = rng.randrange(n), rng.randrange(n)
            if u != v and not g.has(u, v):
                g.add(u, v); return ("add", (min(u,v),max(u,v)))
        return ("noop", None)
    elif r < 0.65:
        # delete edge only if both endpoints stay >=6
        edges = tuple(g.edges)
        for _ in range(20):
            a, b = rng.choice(edges)
            if g.degree(a) > MIN_DEG and g.degree(b) > MIN_DEG:
                g.remove(a, b); return ("del", (a, b))
        return ("noop", None)
    else:
        # degree-preserving 2-swap (always safe)
        edges = tuple(g.edges)
        if len(edges) < 2: return ("noop", None)
        for _ in range(20):
            a, b = rng.choice(edges); c, d = rng.choice(edges)
            if len({a,b,c,d}) < 4: continue
            opts = [((a,c),(b,d)), ((a,d),(b,c))]
            rng.shuffle(opts)
            for e1, e2 in opts:
                if not g.has(*e1) and not g.has(*e2):
                    g.remove(a,b); g.remove(c,d); g.add(*e1); g.add(*e2)
                    return ("swap", ((min(a,b),max(a,b)),(min(c,d),max(c,d)),
                                     (min(*e1),max(*e1)),(min(*e2),max(*e2))))
        return ("noop", None)


def targeted_add(g, rng):
    ce = [(a, b) for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4]
    if not ce: return ("noop", None)
    e = rng.choice(ce)
    col = three_coloring_of(g, exclude_edge=e)
    if col is None: return ("noop", None)
    by = {0: [], 1: [], 2: []}
    for v in range(g.n): by[col[v]].append(v)
    color = rng.choice([0,1,2]); cand = by[color][:]; rng.shuffle(cand)
    for i in range(len(cand)):
        for j in range(i+1, len(cand)):
            x, y = cand[i], cand[j]
            if not g.has(x, y):
                g.add(x, y); return ("add", (min(x,y),max(x,y)))
    return ("noop", None)


def undo(g, move):
    kind, data = move
    if kind == "add": g.remove(*data)
    elif kind == "del": g.add(*data)
    elif kind == "swap":
        o1,o2,n1,n2 = data
        g.remove(*n1); g.remove(*n2); g.add(*o1); g.add(*o2)


def anneal_md(g0, rng, iters, T0=5.0, Tend=0.02, tag="", report_every=25000):
    g = g0.copy()
    cur, cur_info = score_md(g)
    best = cur; best_g = g.copy(); best_info = cur_info
    decay = (Tend/T0)**(1.0/max(1,iters)); T = T0; t0 = time.time()
    for it in range(iters):
        mv = safe_move(g, rng)
        if mv[0] == "noop": T *= decay; continue
        new, new_info = score_md(g)
        d = new - cur
        if d <= 0 or rng.random() < math.exp(-d/max(T,1e-9)):
            cur, cur_info = new, new_info
            if new < best:
                best = new; best_g = g.copy(); best_info = new_info
                if best_info[0]==4 and best_info[1]==0 and best_info[2]==0 and best_info[3]>=6:
                    return best, best_g, best_info, it
        else:
            undo(g, mv)
        T *= decay
        if report_every and it % report_every == 0 and it > 0:
            print(f"  [{tag}] it={it} T={T:.2f} cur={cur:.1f} best={best:.1f} "
                  f"info(chi,ncV,crE,minD,maxD)={best_info} ({time.time()-t0:.0f}s)", flush=True)
    return best, best_g, best_info, -1


def main():
    rng = random.Random(909090)
    print("=== count ASSAULT: min-deg>=6 (IRREGULAR allowed) annealer ===")
    print("covers Prop 5.1 feasible region m>3n that strict-6reg excludes\n")
    runs = []
    for n in (12, 13, 14, 15, 16, 17, 18):
        gs = seed_random_regular(n, 6, rng)
        if gs: runs.append((f"md6-n{n}", gs, 120000))
    overall = None; hits = []
    for tag, gs, iters in runs:
        print(f"--- {tag} (n={gs.n}, m={len(gs.edges)}), {iters} iters")
        b, bg, binfo, hit = anneal_md(gs, rng, iters, tag=tag)
        print(f"  => {tag}: best={b:.1f} info(chi,ncV,crE,minD,maxD)={binfo}", flush=True)
        if hit >= 0:
            hits.append((tag, sorted(bg.edges), bg.n))
            print(f"  *** WITNESS CANDIDATE {tag} edges={sorted(bg.edges)} ***", flush=True)
        if overall is None or b < overall[0]:
            overall = (b, tag, binfo, sorted(bg.edges), bg.n)
    print("\n" + "="*60)
    if hits:
        print(f"WITNESS CANDIDATES {len(hits)} — DUAL-VERIFY")
        for t,e,n in hits: print(f"  {t} n={n} edges={e}")
    print(f"OVERALL BEST score={overall[0]:.1f} from {overall[1]} info={overall[2]} n={overall[4]}")
    print(f"edges={overall[3]}")
    print("="*60)


if __name__ == "__main__":
    main()
