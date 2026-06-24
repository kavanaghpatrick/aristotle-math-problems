#!/usr/bin/env python3
"""
forge_sweep_min_critical.py — exhaustive min-critical-edge profile by vertex count.

For each n, stream nauty geng (connected, min-degree>=3), keep only the
4-vertex-critical graphs, and track the MINIMUM number of critical edges and
how many graphs achieve small counts. The headline number per n:
    min over 4-vertex-critical G on n vertices of (#critical edges).
A witness exists at n iff this minimum is 0.

geng filters used:
  -c          connected
  -d3         min degree >= 3   (4-critical => min deg >= k-1 = 3)
We could add an upper edge bound, but keep it permissive.

To keep n=9,10 tractable we exploit: a 4-vertex-critical graph has min degree
>= 3 and (Kostochka-Yancey) m >= (5n-2)/3 edges. We pass -d3 to geng and apply
the KY lower edge bound as an early reject. We also cap chromatic tests with a
fast 3-colorability short-circuit (if 3-colorable, skip).
"""
import sys
import subprocess
import shutil
import os
import networkx as nx
from forge_verify import (is_k_colorable, is_vertex_critical, critical_edges)


GENG = None
for cand in [shutil.which("geng"), "/opt/homebrew/bin/geng",
             "/opt/homebrew/Cellar/nauty/2.9.3/bin/geng"]:
    if cand and os.path.exists(cand):
        GENG = cand
        break


def ky_min_edges(n):
    """Kostochka-Yancey: a 4-critical graph has m >= (5n-2)/3 (ceil)."""
    import math
    return math.ceil((5 * n - 2) / 3)


def is_4_vertex_critical_fast(G):
    """Fast check: chi==4 and vertex-critical. Uses 3/4-colorability short-circuits."""
    # must NOT be 3-colorable, must be 4-colorable
    if is_k_colorable(G, 3):
        return False
    if not is_k_colorable(G, 4):
        return False  # chi >= 5
    # chi == 4. vertex-critical: every G-v is 3-colorable.
    for v in G.nodes():
        H = G.copy()
        H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def num_critical_edges_fast(G):
    """#edges e with chi(G-e)=3, i.e. G-e is 3-colorable."""
    c = 0
    for (u, v) in G.edges():
        H = G.copy()
        H.remove_edge(u, v)
        if is_k_colorable(H, 3):
            c += 1
    return c


def sweep(n, min_edges=None, max_edges=None, stop_at_zero=True, report_every=200000):
    if GENG is None:
        print("geng not found", file=sys.stderr)
        return None
    args = [GENG, "-c", "-d3", str(n)]
    # geng edge-range must be mine:maxe ; supply an explicit max to avoid
    # geng treating a lone "k:" as an exact/odd bound.
    maxe = n * (n - 1) // 2
    if min_edges is not None:
        args.append(f"{min_edges}:{max_edges if max_edges is not None else maxe}")
    print(f"running: {' '.join(args)}")
    proc = subprocess.Popen(args, stdout=subprocess.PIPE, text=True, bufsize=1)
    best = None  # (num_critical, g6, m)
    n_crit = 0
    n_seen = 0
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        n_seen += 1
        if n_seen % report_every == 0:
            print(f"  ... {n_seen} graphs scanned, "
                  f"{n_crit} are 4-vertex-critical, best={best[0] if best else '-'}")
        G = nx.from_graph6_bytes(line.encode())
        if not is_4_vertex_critical_fast(G):
            continue
        n_crit += 1
        nc = num_critical_edges_fast(G)
        if best is None or nc < best[0]:
            best = (nc, line, G.number_of_edges())
            print(f"  n={n}: new min critical_edges={nc} "
                  f"m={G.number_of_edges()} g6={line} "
                  f"redundant={G.number_of_edges()-nc}")
            if nc == 0 and stop_at_zero:
                print(f"  *** WITNESS at n={n}: g6={line} ***")
                proc.terminate()
                return best, n_crit, n_seen
    proc.wait()
    print(f"  n={n}: scanned {n_seen} graphs, {n_crit} 4-vertex-critical, "
          f"MIN critical edges = {best[0] if best else 'NONE'}")
    return best, n_crit, n_seen


if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [8]
    for n in ns:
        me = ky_min_edges(n)
        print(f"\n=== n={n} (KY min edges = {me}) ===")
        sweep(n, min_edges=me)
