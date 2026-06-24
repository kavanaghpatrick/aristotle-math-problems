"""
Lattanzio 2002 needs k-1 COMPOSITE (k-1 = a*b, a,b>1). Open sources do not give
the explicit graph, so we test the STRUCTURAL HYPOTHESIS that the factorization
indexes a product/blow-up whose chromatic number is a*b+1 = k, and locate the
exact reason k-1=3 prime kills it.

Hypotheses tested (each is a standard "factorization-indexed" critical-graph idea):

H1. Categorical (tensor) product K_{a+1} x K_{b+1}: chi(G x H) <= min(chi G, chi H)
    by Hedetniemi-type bounds; NOT a chromatic-raising product. Likely WRONG
    direction but we check.

H2. Lexicographic / blow-up: replace each vertex of an a-structure by a b-clique.
    chi(K_a[K_b]) = a*b. So K_a[K_b] has chi = a*b; to get k = a*b+1 we cone it.

H3. The key observable: ANY construction that produces chi = k by combining an
    a-part and a b-part needs a,b >= 2 to have two non-trivial parts to combine.
    With k-1 prime, one part is forced to size 1 (trivial) and the "combination"
    degenerates. We make this precise by checking: does the no-critical-edge
    REDUNDANCY require >=2 independent obstructions per edge, and does a*b with
    a,b>=2 supply exactly that 2D redundancy that a 1D (prime) structure cannot?

We don't claim to reproduce Lattanzio's exact graph (not in open literature); we
characterize the ARITHMETIC ROLE of compositeness and confirm k=4 (k-1=3) lacks
the 2-dimensional redundancy that all product-type constructions exploit.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges, is_erdos944


def tensor_product(a, b):
    """K_a x K_b categorical product."""
    return nx.tensor_product(nx.complete_graph(a), nx.complete_graph(b))


def lex_blowup(a, b):
    """K_a[K_b] lexicographic product: chi = a*b."""
    return nx.lexicographic_product(nx.complete_graph(a), nx.complete_graph(b))


def cone(G):
    """Add an apex adjacent to all of G. chi(cone) = chi(G)+1."""
    H = G.copy()
    H = nx.convert_node_labels_to_integers(H)
    apex = H.number_of_nodes()
    H.add_node(apex)
    for v in list(H.nodes()):
        if v != apex:
            H.add_edge(apex, v)
    return H


def report(G, name, k=None):
    chi = chromatic_number(G)
    s = f"{name}: n={G.number_of_nodes()}, m={G.number_of_edges()}, chi={chi}"
    if k is not None and chi == k:
        vc = is_vertex_critical(G, k)
        ce = critical_edges(G)
        s += f", vc={vc}, #crit_edges={len(ce)}"
    print(s)
    return chi


if __name__ == "__main__":
    print("=== H1: tensor (categorical) product K_{a+1} x K_{b+1} ===")
    print("    (chromatic-LOWERING product; expect chi small)")
    for (a, b) in [(2, 2), (2, 3), (3, 3)]:
        report(tensor_product(a + 1, b + 1), f"K_{a+1} x K_{b+1}")

    print("\n=== H2: lex blow-up K_a[K_b], chi = a*b; cone -> chi = a*b+1 = k ===")
    for (a, b) in [(2, 2), (2, 3), (3, 2)]:
        G = lex_blowup(a, b)
        k = a * b + 1
        report(G, f"K_{a}[K_{b}] (chi should be {a*b})")
        report(cone(G), f"cone(K_{a}[K_{b}]) (k={k})", k=k)

    print("\n=== k=4 (k-1=3 prime): the only factorizations are 1x3, 3x1 ===")
    print("    a=1: K_1[K_3] = K_3, cone = K_4. a=3,b=1: K_3[K_1]=K_3, cone=K_4.")
    report(cone(lex_blowup(1, 3)), "cone(K_1[K_3]) = cone(K_3) = K_4", k=4)
    report(cone(lex_blowup(3, 1)), "cone(K_3[K_1]) = cone(K_3) = K_4", k=4)
    print("    => prime k-1 forces a trivial (1-dim) factor; the 'product' is just")
    print("       K_3, and cone(K_3)=K_4 which is the MAXIMALLY edge-critical graph")
    print("       (all 6 edges critical). NO 2D redundancy available.")
