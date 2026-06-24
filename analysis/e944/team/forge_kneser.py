#!/usr/bin/env python3
"""
forge_kneser.py — DENSE global-topological χ=4 mechanism: Kneser graphs and
Schrijver graphs.

Kneser graph K(n,k): vertices = k-subsets of [n], adjacent iff disjoint.
χ(K(n,k)) = n − 2k + 2 by the Lovász–Borsuk–Ulam theorem — a GLOBAL TOPOLOGICAL
obstruction (the neighborhood complex is (n−2k)-connected), NOT a local clique.
For χ=4: n = 2k+2. Smallest: K(4,1)=K4, K(6,2), K(8,3), K(10,4)...

These are DENSE (degree of K(n,k) = C(n−k,k)), dodging the sparsity that killed
the projective-quadrangulation seed. The χ=4 reason is topological/global =
exactly the non-vertex-aligned mechanism wanted.

SCHRIJVER graph SG(n,k): the VERTEX-CRITICAL subgraph of K(n,k) — induced on
"stable" k-subsets (no two cyclically-adjacent elements). χ(SG(n,k)) = n−2k+2
still, and SG is vertex-critical (Schrijver 1978)! So SG(2k+2,k) is a
4-CHROMATIC VERTEX-CRITICAL graph from a topological obstruction. EXACTLY a
candidate witness substrate.

TEST: for SG(2k+2,k), k=1,2,3,4: is it 4-vertex-critical? how many critical
edges? Does the topological obstruction survive single-edge deletion?
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def kneser(n, k):
    verts = list(itertools.combinations(range(n), k))
    G = nx.Graph()
    G.add_nodes_from(verts)
    for a, b in itertools.combinations(verts, 2):
        if not (set(a) & set(b)):
            G.add_edge(a, b)
    return G


def is_stable_cyclic(s, n):
    """s is a stable k-subset: no two elements cyclically adjacent mod n
    (i and i+1 mod n not both in s)."""
    ss = set(s)
    for i in s:
        if (i + 1) % n in ss:
            return False
    return True


def schrijver(n, k):
    verts = [c for c in itertools.combinations(range(n), k) if is_stable_cyclic(c, n)]
    G = nx.Graph()
    G.add_nodes_from(verts)
    for a, b in itertools.combinations(verts, 2):
        if not (set(a) & set(b)):
            G.add_edge(a, b)
    return G


def chi(G):
    if G.number_of_nodes() == 0: return 0
    if is_k_colorable(G, 2): return 2
    if is_k_colorable(G, 3): return 3
    if is_k_colorable(G, 4): return 4
    return 5


def report(G, name):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    if n == 0:
        print(f"[{name}] empty"); return None
    degs = sorted(d for _, d in G.degree())
    c = chi(G)
    if c != 4:
        print(f"[{name}] n={n} m={G.number_of_edges()} chi={c} "
              f"mindeg={degs[0]} maxdeg={degs[-1]}", flush=True)
        return None
    vc, _, bad = is_vertex_critical(G, 4)
    ce = critical_edges(G, 4)
    m = G.number_of_edges()
    print(f"[{name}] n={n} m={m} chi=4 mindeg={degs[0]} regular={len(set(degs))==1} "
          f"vc={vc} noncrit_v={len(bad)} |E*|={len(ce)} "
          f"redundant={m-len(ce)} ({100*(m-len(ce))//m if m else 0}%)", flush=True)
    if vc and len(ce) == 0:
        edges = [tuple(sorted(e)) for e in G.edges()]
        if checkers.is_erdos944_k_r1(edges, n, 4):
            print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
            return ("W", G)
    return (len(ce) if vc else None, G)


if __name__ == "__main__":
    print("=== Kneser graphs K(2k+2,k), chi=4 by Borsuk-Ulam (DENSE, global) ===", flush=True)
    for k in (1, 2, 3, 4):
        report(kneser(2 * k + 2, k), f"K({2*k+2},{k})")

    print("\n=== Schrijver graphs SG(2k+2,k) — vertex-critical chi=4 (Schrijver 1978) ===", flush=True)
    for k in (1, 2, 3, 4, 5):
        report(schrijver(2 * k + 2, k), f"SG({2*k+2},{k})")
