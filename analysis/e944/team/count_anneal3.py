#!/usr/bin/env python3
"""
count_anneal3.py — TARGETED de-criticalization annealer (count, E944 ASSAULT).

proximity proved the circulant basin is a hard local trap at critical-count=n/3;
"the SA scorer needs a NON-LOCAL move to escape." This annealer adds a
structure-aware move that directly attacks a chosen critical edge:

  An edge uv is critical  ⟺  χ(G−uv)=3, i.e. there is a proper 3-coloring c of
  G−uv (necessarily c(u)=c(v)). To DE-criticalize uv we want G−uv to stop being
  3-colorable. Heuristic move: take such a 3-coloring c, pick two vertices x,y
  with c(x)=c(y), x≁y, and ADD edge xy. This invalidates THIS coloring c and
  (often) raises χ(G−uv) back to 4 — making uv non-critical — while keeping G
  4-chromatic. We then optionally delete a random edge to control density.

The targeted move is mixed with the random move-set. Soft scorer reused.
Runs at n=12..16 from circulant + random seeds. Dual-verify any score-0 hit.
"""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import (Graph, score, random_move, undo_move,
                          seed_C13_125, seed_random_regular, chi_exact)
import networkx as nx


def three_coloring_of(g, exclude_edge=None):
    """Return a proper 3-coloring (list color[v]) of g (optionally with an edge
    removed), or None if not 3-colorable. Backtracking."""
    n = g.n
    adj = g.adj[:]
    if exclude_edge:
        a, b = exclude_edge
        adj[a] &= ~(1 << b); adj[b] &= ~(1 << a)
    color = [-1]*n
    order = sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))
    def bt(idx):
        if idx == n: return True
        v = order[idx]
        forb = 0; nb = adj[v]
        while nb:
            low = nb & (-nb); u = low.bit_length()-1
            if color[u] >= 0: forb |= (1 << color[u])
            nb ^= low
        for c in range(3):
            if not (forb >> c) & 1:
                color[v] = c
                if bt(idx+1): return True
                color[v] = -1
        return False
    return color if bt(0) else None


def critical_edges_list(g):
    out = []
    for (a, b) in g.edges:
        if g.chi_minus_edge(a, b) < 4:
            out.append((a, b))
    return out


def targeted_move(g, rng):
    """Pick a critical edge, find a 3-coloring of G-e, add an edge between two
    same-colored non-adjacent vertices to break it. Returns move record or noop."""
    ce = critical_edges_list(g)
    if not ce:
        return ("noop", None)
    e = rng.choice(ce)
    col = three_coloring_of(g, exclude_edge=e)
    if col is None:
        return ("noop", None)
    # same-colored non-adjacent pairs
    by_color = {0: [], 1: [], 2: []}
    for v in range(g.n):
        by_color[col[v]].append(v)
    rng_color = rng.choice([0, 1, 2])
    cand = by_color[rng_color]
    rng.shuffle(cand)
    for i in range(len(cand)):
        for j in range(i+1, len(cand)):
            x, y = cand[i], cand[j]
            if not g.has(x, y):
                g.add(x, y)
                return ("add", (min(x, y), max(x, y)))
    return ("noop", None)


def mixed_move(g, rng, p_targeted=0.4):
    if rng.random() < p_targeted:
        mv = targeted_move(g, rng)
        if mv[0] != "noop":
            return mv
    return random_move(g, rng)


def anneal_targeted(g0, rng, iters, T0=4.0, Tend=0.02, tag="", report_every=20000):
    g = g0.copy()
    cur, cur_info = score(g)
    best = cur; best_g = g.copy(); best_info = cur_info
    decay = (Tend/T0) ** (1.0/max(1, iters))
    T = T0; t0 = time.time()
    for it in range(iters):
        mv = mixed_move(g, rng)
        if mv[0] == "noop":
            T *= decay; continue
        new, new_info = score(g)
        d = new - cur
        if d <= 0 or rng.random() < math.exp(-d/max(T, 1e-9)):
            cur, cur_info = new, new_info
            if new < best:
                best = new; best_g = g.copy(); best_info = new_info
                if best_info == (4, 0, 0):
                    return best, best_g, best_info, it
        else:
            undo_move(g, mv)
        T *= decay
        if report_every and it % report_every == 0 and it > 0:
            print(f"  [{tag}] it={it} T={T:.3f} cur={cur:.1f} best={best:.1f} "
                  f"info={best_info} ({time.time()-t0:.0f}s)", flush=True)
    return best, best_g, best_info, -1


def main():
    rng = random.Random(31337)
    print("=== count ASSAULT annealer 3: TARGETED de-criticalization moves ===")
    print("(non-local move to escape proximity's circulant basin trap)\n")
    runs = [("C13(1,2,5)", seed_C13_125(), 80000)]
    for n in (12, 13, 14, 15, 16):
        gs = seed_random_regular(n, 6, rng)
        if gs: runs.append((f"rand6reg-n{n}", gs, 80000))
    overall = None; hits = []
    for tag, gs, iters in runs:
        print(f"--- {tag} (n={gs.n}, m={len(gs.edges)}), {iters} iters (40% targeted)")
        b, bg, binfo, hit = anneal_targeted(gs, rng, iters, tag=tag)
        print(f"  => {tag}: best={b:.1f} info(chi,noncritV,critE)={binfo}", flush=True)
        if hit >= 0:
            hits.append((tag, sorted(bg.edges), bg.n))
            print(f"  *** WITNESS CANDIDATE {tag} edges={sorted(bg.edges)} ***", flush=True)
        if overall is None or b < overall[0]:
            overall = (b, tag, binfo, sorted(bg.edges), bg.n)
    print("\n" + "="*60)
    if hits:
        print(f"WITNESS CANDIDATES {len(hits)} — DUAL-VERIFY")
        for t, e, n in hits: print(f"  {t} n={n} edges={e}")
    print(f"OVERALL BEST score={overall[0]:.1f} from {overall[1]} info={overall[2]} n={overall[4]}")
    print(f"edges={overall[3]}")
    print("="*60)


if __name__ == "__main__":
    main()
