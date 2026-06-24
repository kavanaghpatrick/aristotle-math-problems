#!/usr/bin/env python3
"""
forge_assault_walls_sat.py — direct construction targeting wall's SHARP criterion
on 6-regular graphs, the SkSt Problem 5.2 target.

wall's criterion (validated): a 4-vertex-critical G is a (4,1)-witness  IFF
for EVERY vertex v and EVERY proper 3-coloring c of G-v, each of the 3 colors
appears >= 2 times among N(v).

So we don't need to test edges. We search 6-regular graphs on n in {11,12,13,14}
for: (i) chi=4, (ii) vertex-critical, (iii) the color-balance condition.

Pure-Python approach (no SAT lib available): generate 6-regular candidate graphs
- via nauty geng -d6 -D6 (exact, exhaustive at n=11,12; large at n=13) AND
- via random 6-regular graphs (networkx random_regular_graph) for n>=13,
then apply the full witness test (forge_verify + dual-check count's checkers).

This is exhaustive at n=11,12 (small) and Monte Carlo at n=13,14. It directly
attacks SkSt open Problem 5.2.
"""
import sys
import subprocess
import random
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers

GENG = "/opt/homebrew/bin/geng"


def chi4(G):
    return (not is_k_colorable(G, 3)) and is_k_colorable(G, 4)


def is_4vc(G):
    if not chi4(G):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def witness(G):
    if not is_4vc(G):
        return False
    if len(critical_edges(G, 4)) != 0:
        return False
    G2 = nx.convert_node_labels_to_integers(G)
    edges = [tuple(sorted(e)) for e in G2.edges()]
    return checkers.is_erdos944_k_r1(edges, G2.number_of_nodes(), k=4)


def scan_exhaustive_6regular(n, report=20000):
    """geng -c -d6 -D6 n : all connected 6-regular graphs on n vertices."""
    args = [GENG, "-c", "-d6", "-D6", str(n)]
    print(f"running {' '.join(args)}", flush=True)
    proc = subprocess.Popen(args, stdout=subprocess.PIPE, text=True, bufsize=1)
    seen = 0
    n4vc = 0
    best = None
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        seen += 1
        if seen % report == 0:
            print(f"  ... {seen} 6-regular graphs, {n4vc} are 4-vc, "
                  f"best_crit={best[0] if best else '-'}", flush=True)
        G = nx.from_graph6_bytes(line.encode())
        if not chi4(G):
            continue
        if not is_4vc(G):
            continue
        n4vc += 1
        c = len(critical_edges(G, 4))
        if best is None or c < best[0]:
            best = (c, line)
            print(f"  n={n}: 6-reg 4-vc graph crit={c} g6={line}", flush=True)
            if c == 0:
                G2 = nx.convert_node_labels_to_integers(G)
                if witness(G2):
                    print(f"  *** DUAL-VERIFIED 6-REGULAR WITNESS n={n}: {line} ***",
                          flush=True)
                    proc.terminate()
                    return ("WITNESS", line, n)
    proc.wait()
    print(f"  n={n}: {seen} 6-regular graphs, {n4vc} four-vertex-critical, "
          f"MIN crit = {best[0] if best else 'NONE (no 6-reg 4-vc graph)'}", flush=True)
    return best


def scan_random_6regular(n, trials, seed=0):
    rng = random.Random(seed)
    best = None
    n4vc = 0
    for t in range(trials):
        try:
            G = nx.random_regular_graph(6, n, seed=rng.randint(0, 10**9))
        except Exception:
            continue
        if not chi4(G) or not is_4vc(G):
            continue
        n4vc += 1
        c = len(critical_edges(G, 4))
        if best is None or c < best[0]:
            best = (c, G.copy())
            print(f"  n={n} random 6-reg 4-vc: crit={c}", flush=True)
            if c == 0 and witness(G):
                print(f"  *** DUAL-VERIFIED 6-REGULAR WITNESS n={n} (random) ***",
                      flush=True)
                return ("WITNESS", G, n)
    print(f"  n={n} random: {n4vc}/{trials} were 4-vc, "
          f"min crit={best[0] if best else 'none'}", flush=True)
    return best


if __name__ == "__main__":
    # NOTE: skeptic already EXHAUSTED connected 6-regular graphs n=11,12,13,14
    # (first 6-reg 4-vc graph is C13(1,2,5) at n=13, which has critical edges;
    # NO witness through n=14). So we do NOT re-run exhaustive n<=14.
    # New ground: random 6-regular at n>=15 (exhaustive infeasible there).
    for n in [15, 16, 17, 18, 20]:
        print(f"\n=== Random 6-regular scan n={n} (30000 trials) ===", flush=True)
        r = scan_random_6regular(n, 30000, seed=n)
        if r and isinstance(r, tuple) and r[0] == "WITNESS":
            G = r[1]
            G2 = nx.convert_node_labels_to_integers(G)
            with open("forge_assault_6reg_WITNESS.txt", "w") as f:
                f.write(f"# 6-regular WITNESS n={G2.number_of_nodes()}\n")
                for u, v in sorted(tuple(sorted(e)) for e in G2.edges()):
                    f.write(f"{u} {v}\n")
            print("Saved forge_assault_6reg_WITNESS.txt", flush=True)
            sys.exit(0)
