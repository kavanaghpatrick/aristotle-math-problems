#!/usr/bin/env python3
"""
forge_double_cover.py — principled asymmetric construction targeting the EXACT
k=4 spec (per jensen's dissection):

  Build a 4-vertex-critical graph where every edge is covered by >=2 INDEPENDENT
  4-coloring obstructions (so deleting any one edge leaves >=1 obstruction intact
  => no critical edge), WITHOUT relying on (a) factorization of k-1=3, or (b) a
  long circulant distance, and WITH broken vertex-transitivity.

GADGET CHOICE: the Moser spindle and overlapping odd wheels are minimal 4-chromatic
rigid units. We assemble MANY 4-chromatic "obstruction units" sharing edges so that
each shared edge sits in >=2 units, then prune to vertex-critical.

Concretely we test families:
  (A) Two odd wheels W_{2t+1} sharing a path / sharing their hubs differently.
  (B) Stacked Moser spindles glued along edges.
  (C) A "book" of triangles plus a 4-chromatic frame: many triangles sharing a
      common edge create redundancy for that edge but we need it for ALL edges.
  (D) Generalized: take a 3-chromatic graph C (odd cycle / Mycielski-free), and
      build the "biwheel" — two apexes a,b each joined to all of C, plus edge ab.
      Then a,b,and C interact. Tune C and apex adjacencies to kill all critical
      edges while staying vertex-critical.

All candidates verified exactly with forge_verify.
"""
import itertools
import networkx as nx
from forge_verify import (chromatic_number, is_vertex_critical, critical_edges,
                          is_k_colorable, is_e944_witness, summary)


def odd_wheel(t):
    """Wheel on an odd cycle C_{2t+1} plus a hub. chi=4."""
    G = nx.cycle_graph(2 * t + 1)
    hub = 2 * t + 1
    for v in range(2 * t + 1):
        G.add_edge(hub, v)
    return G


def moser_spindle():
    G = nx.Graph()
    edges = [(0,1),(0,2),(1,2),(0,3),(0,4),(3,4),(1,5),(3,5),(2,6),(4,6),(5,6)]
    # standard Moser spindle (7 vertices, 11 edges, chi=4, unit-distance)
    G.add_edges_from(edges)
    return G


def biwheel(cycle_nodes, extra_apex_edges=None):
    """
    Two apexes a, b, both joined to every vertex of an odd cycle C, plus edge a-b.
    C = odd cycle => needs 3 colors; a joined to all of C => a 4th color forced
    around a; b also. The two apexes give TWO obstruction families.
    extra_apex_edges: optional list of (apex, cycle_vertex) to DROP to break
    symmetry / tune criticality.
    """
    n = len(cycle_nodes)
    G = nx.Graph()
    for i in range(n):
        G.add_edge(cycle_nodes[i], cycle_nodes[(i + 1) % n])
    a, b = "a", "b"
    for v in cycle_nodes:
        G.add_edge(a, v)
        G.add_edge(b, v)
    G.add_edge(a, b)
    if extra_apex_edges:
        for (ap, v) in extra_apex_edges:
            if G.has_edge(ap, v):
                G.remove_edge(ap, v)
    return G


def two_wheels_shared_rim(t1, t2, overlap):
    """
    Two odd wheels whose rims share a path of `overlap` vertices. Each wheel is a
    4-chromatic obstruction; shared rim edges are covered by both wheels => those
    edges are redundant. Spoke edges may remain critical.
    """
    W1 = odd_wheel(t1)
    n1 = W1.number_of_nodes()
    W1 = nx.relabel_nodes(W1, {i: ("w1", i) for i in W1.nodes()})
    W2 = odd_wheel(t2)
    W2 = nx.relabel_nodes(W2, {i: ("w2", i) for i in W2.nodes()})
    G = nx.union(W1, W2)
    # identify the first `overlap` rim vertices
    for i in range(overlap):
        G = nx.contracted_nodes(G, ("w1", i), ("w2", i), self_loops=False)
    return nx.convert_node_labels_to_integers(G)


def profile(G, name):
    if is_k_colorable(G, 3):
        print(f"[{name}] chi<=3 (n={G.number_of_nodes()})")
        return
    if not is_k_colorable(G, 4):
        print(f"[{name}] chi>=5 (n={G.number_of_nodes()})")
        return
    vc, _, bad = is_vertex_critical(G, 4)
    ce = critical_edges(G, 4)
    m = G.number_of_edges()
    print(f"[{name}] n={G.number_of_nodes()} m={m} chi=4 vertex_critical={vc} "
          f"(noncrit_v={len(bad)}) critical_edges={len(ce)} "
          f"redundant={m-len(ce)} ({100*(m-len(ce))//m if m else 0}%)")
    if vc and len(ce) == 0:
        print(f"  *** WITNESS: {name} ***")
        is_e944_witness(G)


if __name__ == "__main__":
    print("=== Biwheel family (two apexes over an odd cycle) ===")
    for cn in (3, 5, 7, 9, 11):
        profile(biwheel(list(range(cn))), f"biwheel(C{cn})")

    print("\n=== Biwheel with broken symmetry (drop some apex-rim edges) ===")
    for cn in (5, 7, 9):
        cyc = list(range(cn))
        # drop apex 'a' from vertex 0 and apex 'b' from vertex 1 (asymmetric)
        profile(biwheel(cyc, extra_apex_edges=[("a", 0), ("b", 1)]),
                f"biwheel(C{cn})-asym2")
        profile(biwheel(cyc, extra_apex_edges=[("a", 0), ("b", cn//2)]),
                f"biwheel(C{cn})-asym2b")

    print("\n=== Two odd wheels sharing a rim path ===")
    for (t1, t2, ov) in [(1,1,1),(1,1,2),(2,2,2),(2,2,3),(2,3,2),(3,3,3)]:
        try:
            profile(two_wheels_shared_rim(t1, t2, ov),
                    f"2wheels(t{t1},t{t2},ov{ov})")
        except Exception as e:
            print(f"  2wheels(t{t1},t{t2},ov{ov}) error: {e}")

    print("\n=== Moser spindle ===")
    profile(moser_spindle(), "Moser")
