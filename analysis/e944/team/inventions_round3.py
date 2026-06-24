#!/usr/bin/env python3
"""
inventions_round3.py — count-lane CNT-7 (coloring-space / inverse "blame" object).
(E944 invention blitz R3)

KEY IDEA (new, inverse): an edge e is CRITICAL iff blame(e) > 0, where
  blame(e) = #{ proper-except-e 3-colorings } = #{ 3-colorings of G whose ONLY
  monochromatic edge is e }.
Because χ(G−e)=3 iff G−e has a proper 3-coloring iff G has a 3-coloring monochromatic
only on e. So "no critical edge" ⟺ blame(e)=0 ∀e ⟺ NO 3-coloring has a unique
monochromatic edge. This reframes the witness condition in coloring space.

CNT-7 examines the BLAME DISTRIBUTION: do the 1-conflict 3-colorings spread their
blame across edges with high multiplicity (rigid, hard to kill all) or concentrate
(killable)? And the redundancy question: is every edge in >=2 conflicts among the
minimum-conflict colorings?
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact


def circ(n, S):
    E = []
    for d in S:
        for i in range(n): E.append((i, (i+d) % n))
    return Graph(n, E)


def blame_distribution(g, sample_cap=None):
    """For every 3-coloring (assignment in 3^n), count monochromatic edges; record
    blame(e) = # colorings whose unique monochromatic edge is e. Also tally the
    histogram of #monochromatic-edges over all colorings (min-conflict structure).
    For n up to ~14 we enumerate 3^n / fix color[0]=0 (symmetry) — 3^13/3 ~ 5e5, ok."""
    n = g.n
    edges = list(g.edges)
    blame = {e: 0 for e in edges}
    conflict_hist = {}
    min_conf = None
    # fix vertex 0 to color 0 (symmetry), enumerate rest
    # to keep tractable, enumerate 3^(n-1)
    total = 0
    for assign_tail in itertools.product(range(3), repeat=n-1):
        color = (0,) + assign_tail
        mono = [(a, b) for (a, b) in edges if color[a] == color[b]]
        k = len(mono)
        conflict_hist[k] = conflict_hist.get(k, 0) + 1
        if min_conf is None or k < min_conf:
            min_conf = k
        if k == 1:
            blame[mono[0]] += 1
        total += 1
        if sample_cap and total >= sample_cap:
            break
    return blame, conflict_hist, min_conf, total


def run_cnt7():
    print("### CNT-7 blame-cover (coloring-space inverse object) ###")
    for name, g in [("C13(1,2,5)", circ(13, [1,2,5]))]:
        blame, hist, minc, tot = blame_distribution(g)
        crit_by_blame = [e for e, b in blame.items() if b > 0]
        nz = sorted([b for b in blame.values() if b > 0])
        print(f"  {name}: enumerated {tot} 3-colorings (vertex0 fixed)")
        print(f"  min #monochromatic edges over all 3-colorings = {minc} "
              f"(0 would mean 3-colorable; {minc}>0 confirms χ=4)")
        print(f"  conflict histogram (k monochromatic edges -> count), low end: "
              f"{ {k:hist[k] for k in sorted(hist)[:4]} }")
        print(f"  #edges with positive blame (= critical edges) = {len(crit_by_blame)}")
        print(f"  blame multiplicities of critical edges (sorted): {nz}")
        if nz:
            print(f"  blame range: min={min(nz)} max={max(nz)} -- "
                  f"{'CONCENTRATED (few high-blame edges, killable target)' if max(nz)>3*min(nz) else 'UNIFORM (every critical edge equally blamed -> rigid, kill-one-revive-another)'}")
        # the inverse insight: minc=1 means there exist 1-conflict colorings; each
        # blames exactly one edge. For a witness we need ZERO 1-conflict colorings
        # (min-conflict >= 2). Does any near-witness push min-conflict to 2?
        print(f"  WITNESS in this language: need min-conflict >= 2 (no 1-conflict coloring).")
        print(f"  C13(1,2,5) has min-conflict = {minc}: "
              f"{'has killable 1-conflict colorings' if minc==1 else 'ALREADY min-conflict>=2!'}")
    print("\n  VERDICT: the blame distribution shows WHY critical edges resist —")
    print("  if uniform & every edge blamed by the SAME count, killing one 1-conflict")
    print("  coloring (via an edit) just shifts blame to another edge (rigid).")


def run_cnt7_search(n=13, iters=4000):
    """Mini-search: minimize the number of 1-conflict colorings (=Σ_e [blame>0] weighted)
    over degree-preserving swaps from C_n(1,2,5). Does min-conflict ever reach 2?"""
    import random, math
    print(f"\n### CNT-7 search: minimize 1-conflict colorings, n={n} ###")
    from inventions_round2 import two_swap, undo_swap
    rng = random.Random(7)
    g = circ(n, [1,2,5])
    def score(gg):
        chi = chi_exact(gg.adj, gg.n)
        if chi != 4:
            return 10000 + 100*abs(chi-4)
        ncv = sum(1 for v in range(gg.n) if gg.chi_minus_vertex(v) >= 4)
        mind = min(gg.degree(v) for v in range(gg.n))
        blame, hist, minc, tot = blame_distribution(gg)
        one_conf = hist.get(1, 0)  # number of 1-conflict colorings = total blame
        pen = 0 if mind >= 6 else 50*(6-mind)
        # minimize 1-conflict colorings + vertex-criticality debt
        return one_conf + 20*ncv + pen
    cur = score(g); best = cur; bg = g.copy()
    T = 50.0; decay = (0.5/50.0)**(1/iters)
    for it in range(iters):
        mv = two_swap(g, rng)
        if mv[0] == "noop": T*=decay; continue
        new = score(g); d = new-cur
        if d <= 0 or rng.random() < math.exp(-d/max(T,1e-9)):
            cur = new
            if new < best: best = new; bg = g.copy()
        else:
            undo_swap(g, mv)
        T *= decay
    blame, hist, minc, tot = blame_distribution(bg)
    ncv = sum(1 for v in range(bg.n) if bg.chi_minus_vertex(v)>=4) if chi_exact(bg.adj,bg.n)==4 else -1
    print(f"  best: 1-conflict colorings={hist.get(1,0)} min-conflict={minc} ncV={ncv} "
          f"minD={min(bg.degree(v) for v in range(bg.n))}")
    print(f"  VERDICT: {'min-conflict pushed to >=2 with vertex-criticality — LEAD!' if minc>=2 and ncv==0 else 'could not reach min-conflict>=2 while vertex-critical'}")


if __name__ == "__main__":
    run_cnt7()
    run_cnt7_search(13, 3000)
