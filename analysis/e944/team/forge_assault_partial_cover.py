#!/usr/bin/env python3
"""
forge_assault_partial_cover.py — interpolate between cover (fat, 0 critical edges,
not vertex-critical) and base (lean, vertex-critical, critical edges) by MERGING
selected twin pairs.

The Z2 voltage cover of C13(1,2,5) has 0 critical edges but every vertex is
removable (its twin backs it up). If we IDENTIFY twin pair (i,0)=(i,1) for a
subset M of base vertices, those merged vertices lose their backup and may become
critical, while unmerged vertices keep their redundancy (edges among them stay
redundant). The hope: a subset M where the merged graph is vertex-critical AND
still has few/zero critical edges.

This is a controlled global move (not local surgery), parameterized by M ⊆ V(base).
We search over M: greedy (merge the vertex that most reduces #removable while
keeping critical low), plus random subsets, plus all small |M|.

Merging twins (i,0),(i,1): contract them; the merged vertex is adjacent to the
union of both twins' neighbors. Self-loops dropped, multiedges collapsed.

All candidates dual-verified.
"""
import itertools
import random
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


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
    return G  # keep (i,a) labels for merging


def merge_twins(Gcov, base_vertices_to_merge):
    """Identify (i,0) with (i,1) for each i in the merge set."""
    G = Gcov.copy()
    for i in base_vertices_to_merge:
        u, v = (i, 0), (i, 1)
        if G.has_node(u) and G.has_node(v):
            G = nx.contracted_nodes(G, u, v, self_loops=False)
    return nx.convert_node_labels_to_integers(G)


def chi4(G):
    return (not is_k_colorable(G, 3)) and is_k_colorable(G, 4)


def removable_count(G):
    c = 0
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if H.number_of_nodes() >= 4 and chi4(H):
            c += 1
    return c


def is_4vc(G):
    if not chi4(G):
        return False
    return removable_count(G) == 0


def crit(G):
    return len(critical_edges(G, 4))


def dual_witness(G):
    if not is_4vc(G) or crit(G) != 0:
        return False
    G2 = nx.convert_node_labels_to_integers(G)
    edges = [tuple(sorted(e)) for e in G2.edges()]
    return checkers.is_erdos944_k_r1(edges, G2.number_of_nodes(), k=4)


def greedy_merge(Gcov, base_n, log=""):
    """
    Greedily add base vertices to the merge set M to reduce #removable while
    keeping the graph chi=4. Stop when vertex-critical (0 removable) or no move.
    Track min critical edges among vertex-critical states reached.
    """
    M = set()
    best = None
    base_order = list(range(base_n))
    while True:
        G = merge_twins(Gcov, M)
        if not chi4(G):
            return best
        rc = removable_count(G)
        c = crit(G)
        if rc == 0:
            # vertex-critical boundary
            if best is None or c < best[0]:
                best = (c, G.copy(), frozenset(M))
            return best
        # try adding each unmerged base vertex; pick the one minimizing
        # (resulting removable count, then critical count)
        cand = [i for i in base_order if i not in M]
        scored = []
        for i in cand:
            G2 = merge_twins(Gcov, M | {i})
            if not chi4(G2):
                continue
            scored.append((removable_count(G2), crit(G2), i))
        if not scored:
            if best is None or c < best[0]:
                best = (c, G.copy(), frozenset(M))
            return best
        scored.sort()
        # record intermediate if it's vertex-critical-ish improvement
        M.add(scored[0][2])


def random_merge(Gcov, base_n, trials, seed=0):
    rng = random.Random(seed)
    best = None
    for t in range(trials):
        k = rng.randint(1, base_n)
        M = set(rng.sample(range(base_n), k))
        G = merge_twins(Gcov, M)
        if not is_4vc(G):
            continue
        c = crit(G)
        if best is None or c < best[0]:
            best = (c, G.copy(), frozenset(M))
            print(f"  random t{t}: |M|={k} n={G.number_of_nodes()} "
                  f"m={G.number_of_edges()} critical_edges={c} VC=True", flush=True)
            if c == 0 and dual_witness(G):
                print("  *** DUAL-VERIFIED WITNESS (partial cover) ***", flush=True)
                return best
    return best


if __name__ == "__main__":
    base_S = (1, 2, 5); base_n = 13
    covers = [
        ("Z2(0,0,1)", voltage_cover(13, base_S, 2, {1:0,2:0,5:1})),
        ("Z2(1,0,0)", voltage_cover(13, base_S, 2, {1:1,2:0,5:0})),
        ("Z2(0,1,0)", voltage_cover(13, base_S, 2, {1:0,2:1,5:0})),
        ("Z2(1,1,0)", voltage_cover(13, base_S, 2, {1:1,2:1,5:0})),
        ("Z2(1,0,1)", voltage_cover(13, base_S, 2, {1:1,2:0,5:1})),
    ]
    overall = None
    for name, Gcov in covers:
        print(f"\n=== Partial-cover merge from {name} ===", flush=True)
        gb = greedy_merge(Gcov, base_n, log=name)
        if gb:
            print(f"  greedy boundary: n={gb[1].number_of_nodes()} "
                  f"critical_edges={gb[0]} |M|={len(gb[2])} VC={is_4vc(gb[1])}",
                  flush=True)
            if gb[0] == 0 and dual_witness(gb[1]):
                print(f"  *** WITNESS via greedy ({name}) ***", flush=True)
                overall = (0, gb[1].copy(), name); break
            if overall is None or gb[0] < overall[0]:
                overall = (gb[0], gb[1].copy(), name)
        rb = random_merge(Gcov, base_n, trials=3000, seed=hash(name) % 1000)
        if rb and (overall is None or rb[0] < overall[0]):
            overall = (rb[0], rb[1].copy(), name)
            if rb[0] == 0 and dual_witness(rb[1]):
                break
    if overall:
        print(f"\nBEST partial-cover: critical_edges={overall[0]} from {overall[2]} "
              f"n={overall[1].number_of_nodes()} VC={is_4vc(overall[1])}", flush=True)
        G2 = nx.convert_node_labels_to_integers(overall[1])
        tag = "WITNESS" if overall[0] == 0 and dual_witness(overall[1]) else f"best_c{overall[0]}"
        with open(f"forge_assault_partialcover_{tag}.txt", "w") as f:
            f.write(f"# partial cover from {overall[2]}: n={G2.number_of_nodes()} "
                    f"m={G2.number_of_edges()} crit={overall[0]} VC={is_4vc(G2)}\n")
            for u, v in sorted(tuple(sorted(e)) for e in G2.edges()):
                f.write(f"{u} {v}\n")
        print(f"Saved forge_assault_partialcover_{tag}.txt", flush=True)
