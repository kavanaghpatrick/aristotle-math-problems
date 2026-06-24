#!/usr/bin/env python3
"""
forge_assault_trim.py — approach from the REDUNDANT side and walk to the
vertex-critical boundary.

We now have a robust source of χ=4 graphs with 0 critical edges that are NOT
vertex-critical: voltage covers of C13(1,2,5) (n=26/39, all edges redundant, all
vertices removable) AND asymmetric biwheels. Their problem is they're too fat:
deleting a vertex leaves a twin carrying the obstruction, so vertices are
redundant.

TRIM: repeatedly delete a REMOVABLE vertex (one whose deletion keeps χ=4). Each
deletion removes redundancy. Track critical-edge count along the way. The DREAM
path reaches a vertex-critical graph (no removable vertex) while critical edges
stay 0 -> WITNESS.

Two strategies:
  (A) GREEDY-MIN-CRITICAL: at each step, among removable vertices, delete the one
      that keeps critical-edge count LOWEST after deletion.
  (B) GREEDY-PRESERVE-ZERO: prefer deletions that keep critical edges == 0; only if
      none, take the min-increase. This biases the walk to stay on the
      zero-critical-edge surface as long as possible.
  (C) Randomized multi-restart over deletion orders.

Every candidate at the vertex-critical boundary is dual-verified (forge_verify +
count's checkers).
"""
import random
import networkx as nx
from forge_verify import (is_k_colorable, is_vertex_critical, critical_edges)
import checkers


def circ(n, S):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for i in range(n):
        for s in S:
            G.add_edge(i, (i + s) % n)
    return G


def voltage_cover(n, S, m, volt_by_len):
    def L(u, v):
        d = (u - v) % n; return min(d, n - d)
    G = nx.Graph()
    for i in range(n):
        for a in range(m):
            G.add_node((i, a))
    for i in range(n):
        for s in S:
            j = (i + s) % n
            volt = volt_by_len.get(L(i, j), 0)
            for a in range(m):
                G.add_edge((i, a), (j, (a + volt) % m))
    return nx.convert_node_labels_to_integers(G)


def biwheel(cyc_n, drop):
    G = nx.Graph()
    for i in range(cyc_n):
        G.add_edge(i, (i + 1) % cyc_n)
    for v in range(cyc_n):
        G.add_edge("a", v); G.add_edge("b", v)
    G.add_edge("a", "b")
    for ap, v in drop:
        if G.has_edge(ap, v):
            G.remove_edge(ap, v)
    return nx.convert_node_labels_to_integers(G)


def chi4(G):
    return (not is_k_colorable(G, 3)) and is_k_colorable(G, 4)


def removable(G):
    out = []
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if H.number_of_nodes() >= 4 and chi4(H):
            out.append(v)
    return out


def crit(G):
    return len(critical_edges(G, 4))


def is_4vc(G):
    if not chi4(G):
        return False
    return len(removable(G)) == 0


def dual_witness(G):
    if not is_4vc(G) or crit(G) != 0:
        return False
    G2 = nx.convert_node_labels_to_integers(G)
    edges = [tuple(sorted(e)) for e in G2.edges()]
    return checkers.is_erdos944_k_r1(edges, G2.number_of_nodes(), k=4)


def trim_walk(G0, mode="preserve_zero", rng=None, log=""):
    """Walk down by deleting removable vertices until vertex-critical."""
    G = nx.convert_node_labels_to_integers(G0)
    steps = 0
    while True:
        rem = removable(G)
        c = crit(G)
        if not rem:
            # vertex-critical boundary
            return G, c
        # choose next deletion
        cand = []
        for v in rem:
            H = G.copy(); H.remove_node(v)
            cand.append((crit(H), v))
        if mode == "preserve_zero":
            zeros = [v for cc, v in cand if cc == 0]
            if zeros:
                pick = (rng.choice(zeros) if rng else zeros[0])
            else:
                mn = min(cc for cc, _ in cand)
                picks = [v for cc, v in cand if cc == mn]
                pick = (rng.choice(picks) if rng else picks[0])
        elif mode == "min_critical":
            mn = min(cc for cc, _ in cand)
            picks = [v for cc, v in cand if cc == mn]
            pick = (rng.choice(picks) if rng else picks[0])
        else:  # random
            pick = (rng.choice(rem) if rng else rem[0])
        G = nx.convert_node_labels_to_integers(
            (lambda H: (H.remove_node(pick), H)[1])(G.copy()))
        steps += 1
        if steps > 200:
            return G, crit(G)


def run(seed_graphs, restarts=40):
    best = None
    for name, G0 in seed_graphs:
        print(f"\n=== Trimming {name} (n={G0.number_of_nodes()} "
              f"m={G0.number_of_edges()} crit={crit(G0)}) ===", flush=True)
        seen_best = None
        for mode in ("preserve_zero", "min_critical", "random"):
            rng = random.Random(0)
            for r in range(restarts if mode == "random" else
                           (restarts if mode == "preserve_zero" else 8)):
                rr = random.Random(r * 13 + 1)
                G, c = trim_walk(G0, mode=mode, rng=rr, log=name)
                if seen_best is None or c < seen_best[0]:
                    seen_best = (c, G.copy(), mode, r)
                    print(f"  [{mode} r{r}] boundary: n={G.number_of_nodes()} "
                          f"m={G.number_of_edges()} critical_edges={c} "
                          f"vertex_critical={is_4vc(G)}", flush=True)
                    if c == 0 and is_4vc(G):
                        if dual_witness(G):
                            print(f"  *** DUAL-VERIFIED WITNESS ({name}) ***", flush=True)
                            return (0, G.copy(), name)
                        else:
                            print("  (0+vc but dual-verify FALSE — investigate)", flush=True)
        if seen_best and (best is None or seen_best[0] < best[0]):
            best = (seen_best[0], seen_best[1].copy(), name)
    return best


if __name__ == "__main__":
    seeds = []
    # voltage covers with 0 critical edges
    seeds.append(("Z2cover(1,2,5)=(0,0,1)", voltage_cover(13, (1,2,5), 2, {1:0,2:0,5:1})))
    seeds.append(("Z2cover(1,2,5)=(1,0,0)", voltage_cover(13, (1,2,5), 2, {1:1,2:0,5:0})))
    seeds.append(("Z2cover(1,2,5)=(0,1,0)", voltage_cover(13, (1,2,5), 2, {1:0,2:1,5:0})))
    # asymmetric biwheels (0 critical, not vc)
    seeds.append(("biwheel(C7) drop a0,b1", biwheel(7, [("a",0),("b",1)])))
    seeds.append(("biwheel(C9) drop a0,b1", biwheel(9, [("a",0),("b",1)])))
    seeds.append(("biwheel(C11) drop a0,b1", biwheel(11, [("a",0),("b",1)])))

    best = run(seeds, restarts=30)
    print(f"\nOVERALL BEST: critical_edges={best[0]} from {best[2]} "
          f"n={best[1].number_of_nodes()} m={best[1].number_of_edges()} "
          f"vertex_critical={is_4vc(best[1])}", flush=True)
    G = best[1]
    G2 = nx.convert_node_labels_to_integers(G)
    tag = "WITNESS" if best[0] == 0 and dual_witness(G) else f"best_c{best[0]}"
    with open(f"forge_assault_trim_{tag}.txt", "w") as f:
        f.write(f"# trim best from {best[2]}: n={G2.number_of_nodes()} "
                f"m={G2.number_of_edges()} critical_edges={best[0]} "
                f"vertex_critical={is_4vc(G2)}\n")
        for u, v in sorted(tuple(sorted(e)) for e in G2.edges()):
            f.write(f"{u} {v}\n")
    print(f"Saved forge_assault_trim_{tag}.txt", flush=True)
