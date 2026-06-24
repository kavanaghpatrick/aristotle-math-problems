#!/usr/bin/env python3
"""
count_basinhop.py — BASIN-HOPPING annealer on the 6-regular manifold (count, E944).

proximity proved C13(1,2,5) is a RIGID PLATEAU: all single-adds lose vertex-
criticality, all degree-preserving 2-swaps stay pinned at 13 critical edges. The
escape lever (proximity): LARGE-STEP moves that break the {1,2} co-difference
structure — simultaneously reshuffle MANY edges at once, then re-settle locally.

This annealer does basin hopping: from the current best, apply a BIG perturbation
(a batch of k degree-preserving 2-swaps, k=3..8, accepted unconditionally), then
run a short local SA to re-settle, and keep the best basin found. Stays exactly
6-regular throughout (every move is degree-preserving), so any score-0 hit is a
genuine 6-regular (4,1)-witness.
"""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, seed_random_regular
from count_anneal_6reg import score_6reg, two_swap, targeted_two_swap, undo_swap
from count_anneal3 import three_coloring_of


def big_perturbation(g, rng, k):
    """Apply k degree-preserving 2-swaps unconditionally (large jump). No undo."""
    applied = 0
    for _ in range(k * 4):
        mv = two_swap(g, rng)
        if mv[0] != "noop":
            applied += 1
            if applied >= k:
                break


def local_resettle(g, rng, iters, T0=1.5, Tend=0.02, p_targeted=0.5):
    """Short local SA (small + targeted moves) to settle into a nearby minimum."""
    cur, cur_info = score_6reg(g)
    best = cur; best_g = g.copy(); best_info = cur_info
    decay = (Tend/T0) ** (1.0/max(1, iters)); T = T0
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
                    return best, best_g, best_info, True
        else:
            undo_swap(g, mv)
        T *= decay
    return best, best_g, best_info, False


def basin_hop(g0, rng, hops, resettle_iters=4000, tag=""):
    g = g0.copy()
    best, best_g, best_info, hit = local_resettle(g, rng, resettle_iters)
    if hit:
        return best, best_g, best_info, 0
    t0 = time.time()
    for h in range(hops):
        # jump from current best with a perturbation of growing size
        g = best_g.copy()
        k = rng.randint(3, 9)
        big_perturbation(g, rng, k)
        b, bg, binfo, hh = local_resettle(g, rng, resettle_iters)
        if hh:
            return b, bg, binfo, h
        if b < best:
            best, best_g, best_info = b, bg, binfo
        if h % 20 == 0:
            print(f"  [{tag}] hop={h} best={best:.1f} info(chi,ncV,crE)={best_info} "
                  f"({time.time()-t0:.0f}s)", flush=True)
    return best, best_g, best_info, -1


def main():
    rng = random.Random(13579)
    print("=== count BASIN-HOPPING annealer (6-regular, large-step escape) ===")
    print("per proximity: break the rigid n/3 plateau with multi-swap jumps\n")
    # seed from circulant champions (on the plateau) + random 6-regular
    def circ(n, S):
        E = []
        for d in S:
            for i in range(n): E.append((i, (i+d) % n))
        return Graph(n, E)
    runs = [("C13(1,2,5)-hop", circ(13, [1,2,5]), 200),
            ("C16(1,2,5)-hop", circ(16, [1,2,5]), 150),
            ("C19(1,2,5)-hop", circ(19, [1,2,5]), 120)]
    for n in (13, 14, 15, 16, 17):
        gs = seed_random_regular(n, 6, rng)
        if gs: runs.append((f"rand6reg-n{n}-hop", gs, 120))
    overall = None; hits = []
    for tag, gs, hops in runs:
        print(f"--- {tag} (n={gs.n}, m={len(gs.edges)}), {hops} hops")
        b, bg, binfo, hit = basin_hop(gs, rng, hops, tag=tag)
        reg = all(bg.degree(v) == 6 for v in range(bg.n))
        print(f"  => {tag}: best={b:.1f} info(chi,ncV,crE)={binfo} 6-reg={reg}", flush=True)
        if hit >= 0:
            hits.append((tag, sorted(bg.edges), bg.n))
            print(f"  *** 6-REG WITNESS CANDIDATE {tag} edges={sorted(bg.edges)} ***", flush=True)
        if overall is None or b < overall[0]:
            overall = (b, tag, binfo, sorted(bg.edges), bg.n)
    print("\n" + "="*60)
    if hits:
        print(f"6-REGULAR WITNESS CANDIDATES {len(hits)} — DUAL-VERIFY IMMEDIATELY")
        for t, e, n in hits: print(f"  {t} n={n} edges={e}")
    print(f"OVERALL BEST score={overall[0]:.1f} from {overall[1]} info={overall[2]} n={overall[4]}")
    print(f"  (min critical-edge count reached on 6-reg manifold via basin-hopping)")
    if overall[2] == (4, 0, 0):
        print("  *** SCORE 0 — WITNESS ***")
    else:
        ncrit = overall[2][2] if overall[2][0]==4 and overall[2][1]==0 else 'N/A(infeasible)'
        print(f"  min feasible critical-edge count found: {ncrit}")
    print("="*60)


if __name__ == "__main__":
    main()
