#!/usr/bin/env python3
"""
count_anneal_6reg.py — DEGREE-PRESERVING annealer on the 6-REGULAR manifold.
(count, E944 ASSAULT — the decisive version)

WHY: anneal1-4 reached 9-10 critical edges but ONLY by dropping min-degree below 6
(E* study + diagnosis: the score-9 graph had deg-seq min 4). Such graphs can NEVER
be witnesses (Prop 5.1: witness needs min-deg >= 6). Steiner's Problem 5.2 names the
6-REGULAR case as the canonical target. So we search EXACTLY the 6-regular manifold:
start 6-regular, use ONLY degree-preserving 2-swaps (remove ab, cd; add ac, bd),
which keeps every vertex at degree 6 forever. The graph stays a valid witness
CANDIDATE class throughout; score = #critical edges (+ soft χ/vertex-crit penalties).

A score-0 here is a genuine 6-regular (4,1)-witness = answer to Steiner Problem 5.2.
"""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, seed_random_regular, chi_exact
from count_anneal3 import three_coloring_of
import networkx as nx

W_CHI = 60.0
W_VC = 12.0


def score_6reg(g, want_chi=4):
    """Degree stays 6 by construction; score = chi/vc penalties + critical edges."""
    c = g.chi()
    chi_pen = 0.0
    if c != want_chi:
        chi_pen = W_CHI * (abs(c - want_chi) + (5 if c < want_chi else 0))
    noncrit_v = 0
    if c == want_chi:
        for v in range(g.n):
            if g.chi_minus_vertex(v) >= want_chi:
                noncrit_v += 1
    else:
        noncrit_v = g.n
    crit_e = 0
    if c == want_chi:
        for (a, b) in g.edges:
            if g.chi_minus_edge(a, b) < want_chi:
                crit_e += 1
    return chi_pen + W_VC * noncrit_v + 1.0 * crit_e, (c, noncrit_v, crit_e)


def two_swap(g, rng):
    """Degree-preserving 2-swap: pick edges ab, cd (4 distinct verts), if ac, bd
    are non-edges, replace. Preserves all degrees. Returns move record or noop."""
    if len(g.edges) < 2:
        return ("noop", None)
    edges = tuple(g.edges)
    for _ in range(30):
        a, b = rng.choice(edges)
        c, d = rng.choice(edges)
        if len({a, b, c, d}) < 4:
            continue
        # two pairings; pick one that creates non-edges
        opts = [((a, c), (b, d)), ((a, d), (b, c))]
        rng.shuffle(opts)
        for (e1, e2) in opts:
            if not g.has(*e1) and not g.has(*e2):
                g.remove(a, b); g.remove(c, d)
                g.add(*e1); g.add(*e2)
                return ("swap", ((min(a,b),max(a,b)), (min(c,d),max(c,d)),
                                 (min(*e1),max(*e1)), (min(*e2),max(*e2))))
    return ("noop", None)


def targeted_two_swap(g, rng):
    """Aim a 2-swap at de-criticalizing an edge: find a critical edge uv, 3-color
    G-uv, and 2-swap to add an edge between same-colored verts (breaking the
    coloring) while removing another edge to preserve degree."""
    ce = [(a, b) for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4]
    if not ce:
        return ("noop", None)
    e = rng.choice(ce)
    col = three_coloring_of(g, exclude_edge=e)
    if col is None:
        return ("noop", None)
    by_color = {0: [], 1: [], 2: []}
    for v in range(g.n):
        by_color[col[v]].append(v)
    rng.shuffle(by_color[0]); rng.shuffle(by_color[1]); rng.shuffle(by_color[2])
    # find same-colored non-adjacent x,y to JOIN; and an existing edge to break
    for color in (0, 1, 2):
        cand = by_color[color]
        for i in range(len(cand)):
            for j in range(i+1, len(cand)):
                x, y = cand[i], cand[j]
                if g.has(x, y):
                    continue
                # to preserve degree: we add xy, must remove an edge at x and at y,
                # and add an edge between their old neighbors. Simplest: pick edge
                # x-p and y-q (p!=q, not adjacent) and 2-swap (x,p),(y,q)->(x,y),(p,q)
                xn = [w for w in range(g.n) if g.has(x, w)]
                yn = [w for w in range(g.n) if g.has(y, w)]
                rng.shuffle(xn); rng.shuffle(yn)
                for p in xn:
                    for q in yn:
                        if len({x, y, p, q}) < 4: continue
                        if g.has(p, q): continue
                        g.remove(x, p); g.remove(y, q)
                        g.add(x, y); g.add(p, q)
                        return ("swap", ((min(x,p),max(x,p)),(min(y,q),max(y,q)),
                                         (min(x,y),max(x,y)),(min(p,q),max(p,q))))
    return ("noop", None)


def undo_swap(g, move):
    kind, data = move
    if kind != "swap":
        return
    o1, o2, n1, n2 = data
    g.remove(*n1); g.remove(*n2)
    g.add(*o1); g.add(*o2)


def anneal_6reg(g0, rng, iters, T0=5.0, Tend=0.02, p_targeted=0.4,
                tag="", report_every=25000):
    g = g0.copy()
    cur, cur_info = score_6reg(g)
    best = cur; best_g = g.copy(); best_info = cur_info
    decay = (Tend/T0) ** (1.0/max(1, iters))
    T = T0; t0 = time.time()
    for it in range(iters):
        if rng.random() < p_targeted:
            mv = targeted_two_swap(g, rng)
            if mv[0] == "noop":
                mv = two_swap(g, rng)
        else:
            mv = two_swap(g, rng)
        if mv[0] == "noop":
            T *= decay; continue
        new, new_info = score_6reg(g)
        d = new - cur
        if d <= 0 or rng.random() < math.exp(-d / max(T, 1e-9)):
            cur, cur_info = new, new_info
            if new < best:
                best = new; best_g = g.copy(); best_info = new_info
                if best_info == (4, 0, 0):
                    return best, best_g, best_info, it
        else:
            undo_swap(g, mv)
        T *= decay
        if report_every and it % report_every == 0 and it > 0:
            print(f"  [{tag}] it={it} T={T:.2f} cur={cur:.1f} best={best:.1f} "
                  f"info(chi,ncV,crE)={best_info} 6-reg ({time.time()-t0:.0f}s)",
                  flush=True)
    return best, best_g, best_info, -1


def main():
    rng = random.Random(424242)
    print("=== count ASSAULT: DEGREE-PRESERVING 6-REGULAR annealer ===")
    print("Search stays EXACTLY 6-regular (Steiner Problem 5.2). score=#critical edges.\n")
    runs = []
    for n in (12, 13, 14, 15, 16, 17, 18):
        gs = seed_random_regular(n, 6, rng)
        if gs is None: continue
        # verify seed is 6-regular
        assert all(gs.degree(v) == 6 for v in range(n))
        runs.append((f"6reg-n{n}", gs, 120000))
    overall = None; hits = []
    for tag, gs, iters in runs:
        print(f"--- {tag} (n={gs.n}, m={len(gs.edges)}={3*gs.n}?), {iters} iters")
        b, bg, binfo, hit = anneal_6reg(gs, rng, iters, tag=tag)
        # confirm still 6-regular
        reg = all(bg.degree(v) == 6 for v in range(bg.n))
        print(f"  => {tag}: best={b:.1f} info(chi,ncV,crE)={binfo} still-6reg={reg}",
              flush=True)
        if hit >= 0:
            hits.append((tag, sorted(bg.edges), bg.n))
            print(f"  *** WITNESS CANDIDATE {tag} (6-reg!) edges={sorted(bg.edges)} ***",
                  flush=True)
        if overall is None or b < overall[0]:
            overall = (b, tag, binfo, sorted(bg.edges), bg.n)
    print("\n" + "="*60)
    if hits:
        print(f"6-REGULAR WITNESS CANDIDATES {len(hits)} — DUAL-VERIFY IMMEDIATELY")
        for t, e, n in hits: print(f"  {t} n={n} edges={e}")
    print(f"OVERALL BEST score={overall[0]:.1f} from {overall[1]} info={overall[2]} n={overall[4]}")
    print(f"  (this is the min critical-edge count reachable on the 6-regular manifold)")
    print(f"edges={overall[3]}")
    print("="*60)


if __name__ == "__main__":
    main()
