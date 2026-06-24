#!/usr/bin/env python3
"""
estar_study.py — systematic study of how E* (critical-edge subgraph) fragments
as annealing drives the critical-edge count down. (count, E944)

Tests the Jensen-Siggers conjecture (E* connected/spanning of positive size)
against our best near-witnesses. If E* fragments / loses vertices as critical
count drops, that's EXISTENCE intel (approaching E*=∅ = witness). If E* stays
connected+spanning no matter how low the count, that's IMPOSSIBILITY intel.
"""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import seed_C13_125, seed_random_regular
from count_anneal3 import anneal_targeted
from estar_structure import analyze_estar


def main():
    rng = random.Random(2026)
    print("=== E* fragmentation study across near-witnesses ===")
    print("(does E* stay connected+spanning, or fragment toward empty?)\n")
    samples = []
    # several independent targeted chains -> low-score near-witnesses at varied n
    configs = [(13, 4), (14, 3), (15, 3), (16, 3)]  # (n, num restarts)
    for n, reps in configs:
        for rep in range(reps):
            if n == 13 and rep == 0:
                g = seed_C13_125()
            else:
                g = seed_random_regular(n, 6, rng)
                if g is None: continue
            b, bg, binfo, hit = anneal_targeted(g, rng, iters=25000,
                                                report_every=0, tag=f"n{n}r{rep}")
            if binfo[0] == 4 and binfo[1] == 0:  # 4-chromatic & vertex-critical
                samples.append((bg, b, binfo, f"n{n}-rep{rep}"))
                print(f"  sample {f'n{n}-rep{rep}':12s}: score={b:.0f} "
                      f"critE={binfo[2]}")
    print("\n--- E* structure of each near-witness (sorted by critical count) ---")
    samples.sort(key=lambda s: s[2][2])
    rows = []
    for bg, b, binfo, label in samples:
        r = analyze_estar(sorted(bg.edges), bg.n, label)
        rows.append(r)
    print("\n=== FRAGMENTATION SUMMARY (lower critE = closer to witness) ===")
    print(f"{'label':14s} {'critE':>5s} {'spanning':>9s} {'connected':>10s} "
          f"{'comps':>6s} {'untouched_v':>12s}")
    for r in rows:
        print(f"{r['label']:14s} {r['ncrit']:5d} {str(r['spanning']):>9s} "
              f"{str(r['connected']):>10s} {r['ncomp']:6d} {r['untouched']:12d}")
    # verdict
    frag = [r for r in rows if not r['connected'] or not r['spanning']]
    print(f"\nNear-witnesses with FRAGMENTED/non-spanning E*: {len(frag)}/{len(rows)}")
    if frag:
        print("⟹ E* DOES fragment as critical count drops — EXISTENCE-leaning intel")
        print("  (critical edges are NOT forced to stay connected+spanning, contra a")
        print("   strong reading of Jensen-Siggers). The witness direction (E*=∅) is")
        print("   not blocked by a connectivity obstruction at these counts.")
    else:
        print("⟹ E* stays connected+spanning everywhere — supports Jensen-Siggers")
        print("  impossibility intuition.")


if __name__ == "__main__":
    main()
