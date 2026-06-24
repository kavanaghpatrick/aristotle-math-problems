#!/usr/bin/env python3
"""
count_anneal2.py — enhanced assault annealer (count, E944).
Complements count_anneal.py with:
  - LONGER chains + REHEAT restarts (escape local minima)
  - n=12..16 (hunter proved n<=11 dead; live zone is n>=12)
  - TWO seed families approached from OPPOSITE failure modes:
      (A) circulant-like: vertex-critical but ~1/3 critical edges (kill edges' criticality)
      (B) "biwheel/dense": 0 critical edges but NOT vertex-critical (repair vertex-criticality)
  - same soft scorer as count_anneal (reused).
"""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import (Graph, score, random_move, undo_move,
                          seed_C13_125, seed_random_regular, seed_g6, chi_exact)
import networkx as nx


def anneal_reheat(g0, rng, total_iters, n_reheats=5, T0=5.0, Tend=0.02,
                  tag="", report_every=40000):
    """SA with periodic reheating from the global best."""
    g = g0.copy()
    cur, cur_info = score(g)
    best = cur; best_g = g.copy(); best_info = cur_info
    seg = max(1, total_iters // n_reheats)
    t_start = time.time()
    total = 0
    for rh in range(n_reheats):
        # restart segment from best (with a perturbation) on later reheats
        if rh > 0:
            g = best_g.copy()
            # perturb: a few random moves accepted unconditionally
            for _ in range(rng.randint(3, 8)):
                random_move(g, rng)
            cur, cur_info = score(g)
        T = T0; decay = (Tend/T0) ** (1.0/max(1, seg))
        for it in range(seg):
            total += 1
            mv = random_move(g, rng)
            if mv[0] == "noop":
                T *= decay; continue
            new, new_info = score(g)
            d = new - cur
            if d <= 0 or rng.random() < math.exp(-d / max(T, 1e-9)):
                cur, cur_info = new, new_info
                if new < best:
                    best = new; best_g = g.copy(); best_info = new_info
                    if best_info == (4, 0, 0):
                        return best, best_g, best_info, total
            else:
                undo_move(g, mv)
            T *= decay
            if report_every and total % report_every == 0:
                el = time.time()-t_start
                print(f"  [{tag}] total={total} reheat={rh} T={T:.3f} "
                      f"cur={cur:.1f} best={best:.1f} info={best_info} ({el:.0f}s)",
                      flush=True)
    return best, best_g, best_info, -1


def seed_dense_chi4(n, rng, deg=8):
    """A denser graph that is 4-chromatic (NOT necessarily vertex-critical) —
    the 'repair vertex-criticality' starting side. Tries random regular graphs of
    degree `deg` until one has chi exactly 4 (dense enough to be 4-chromatic,
    sparse enough not to be 5)."""
    for _ in range(80):
        d = deg if (deg * n) % 2 == 0 else deg + 1
        try:
            G = nx.random_regular_graph(d, n, seed=rng.randint(0, 10**6))
        except Exception:
            continue
        g = Graph(n, list(G.edges()))
        if g.chi() == 4:
            return g
    # fallback: complement of a sparse graph
    G = nx.complement(nx.cycle_graph(n))
    return Graph(n, list(G.edges()))


def main():
    rng = random.Random(7777)
    print("=== count ASSAULT annealer 2 (reheat, n=12..16, dual seed families) ===\n")
    runs = []
    # Family A: random 6-regular at the live n
    for n in (12, 13, 14, 15, 16):
        gs = seed_random_regular(n, 6, rng)
        if gs: runs.append((f"A-rand6reg-n{n}", gs, 120000))
    # Family B: dense chi=4 (repair vertex-criticality from the other side).
    # degree 7 (between the 6-regular target and over-dense): reliably chi=4.
    for n in (12, 14, 16):
        gs = seed_dense_chi4(n, rng, deg=7)
        if gs: runs.append((f"B-densechi4-n{n}", gs, 120000))

    overall = None
    witness_hits = []
    for tag, gs, iters in runs:
        print(f"--- {tag} (n={gs.n}, m={len(gs.edges)}), {iters} iters w/ reheat")
        b, bg, binfo, hit = anneal_reheat(gs, rng, iters, tag=tag)
        print(f"  => {tag}: best={b:.1f} info(chi,noncritV,critE)={binfo}", flush=True)
        if hit >= 0:
            witness_hits.append((tag, sorted(bg.edges), bg.n))
            print(f"  *** WITNESS CANDIDATE {tag} edges={sorted(bg.edges)} ***", flush=True)
        if overall is None or b < overall[0]:
            overall = (b, tag, binfo, sorted(bg.edges), bg.n)
    print("\n" + "="*60)
    if witness_hits:
        print(f"WITNESS CANDIDATES: {len(witness_hits)} — DUAL-VERIFY IMMEDIATELY")
        for t, e, n in witness_hits:
            print(f"  {t} n={n} edges={e}")
    print(f"OVERALL BEST: score={overall[0]:.1f} from {overall[1]} info={overall[2]} "
          f"n={overall[4]}")
    print(f"edges={overall[3]}")
    print("="*60)


if __name__ == "__main__":
    main()
