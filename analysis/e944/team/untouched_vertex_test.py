#!/usr/bin/env python3
"""
untouched_vertex_test.py — forge's discriminating test (count + forge).
A vertex UNTOUCHED by E* (no incident critical edge) in a 4-vertex-critical graph =
"wall-balanced" vertex = local instance of the witness condition. KEY QUESTION: can
an untouched vertex coexist with degree >=6 (the feasible witness regime)? If untouched
⟹ low-degree always, that's an impossibility constraint; if untouched-at-δ≥6 exists,
that's the existence lead.

We measure, over 4-vertex-critical graphs: which vertices are untouched by E*, and
their DEGREES. Census n<=7 exhaustive (atlas) + dense sampled n=11,12.
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
import networkx as nx


def vc(g): return chi_exact(g.adj,g.n)==4 and all(g.chi_minus_vertex(v)<4 for v in range(g.n))

def critical_edges(g): return [(a,b) for (a,b) in g.edges if g.chi_minus_edge(a,b)<4]

def untouched_vertices(g):
    """Vertices with NO incident critical edge."""
    ce = critical_edges(g)
    touched = set()
    for a,b in ce: touched.add(a); touched.add(b)
    return [v for v in range(g.n) if v not in touched]


def census_test():
    print("### Census n<=7: untouched vertices in 4-vertex-critical graphs ###")
    from networkx.generators.atlas import graph_atlas_g
    atlas = graph_atlas_g()
    any_untouched = []
    for n in range(4, 8):
        gs = [G for G in atlas if G.number_of_nodes()==n
              and chi_exact(*( (lambda gg: (gg.adj,gg.n))(Graph(n,list(G.edges()))) ))==4]
        # filter vertex-critical
        for G in gs:
            g = Graph(n, list(G.edges()))
            if not vc(g): continue
            unt = untouched_vertices(g)
            if unt:
                degs = [g.degree(v) for v in unt]
                any_untouched.append((n, len(unt), degs, max(degs)))
    if any_untouched:
        print(f"  4-vtx-critical graphs WITH untouched vertices: {len(any_untouched)}")
        maxdeg_untouched = max(x[3] for x in any_untouched)
        print(f"  MAX degree of any untouched vertex (n<=7): {maxdeg_untouched}")
        for n,k,degs,md in any_untouched[:8]:
            print(f"    n={n}: {k} untouched vertices, degrees {degs}")
    else:
        print("  NO 4-vtx-critical graph on n<=7 has an untouched vertex (E* always spanning)")
    return any_untouched


def dense_test(n, mindeg, samples, rng):
    """Among dense 4-vtx-critical graphs, find untouched vertices and their degrees."""
    found = []
    for _ in range(samples):
        d = mindeg + (mindeg*n)%2
        try:
            G = nx.random_regular_graph(d, n, seed=rng.randint(0,10**7))
        except Exception:
            continue
        g = Graph(n, list(G.edges()))
        if not vc(g): continue
        unt = untouched_vertices(g)
        if unt:
            degs=[g.degree(v) for v in unt]
            found.append((g, unt, degs))
    return found


def main():
    rng = random.Random(2024)
    cu = census_test()
    print("\n### Dense 4-vtx-critical (n=11,12, δ≥6): untouched vertices? ###")
    for n in (11,12):
        found = dense_test(n, 6, 2000, rng)
        if found:
            maxd = max(max(d) for _,_,d in found)
            print(f"  n={n} δ≥6: {len(found)} vertex-critical graphs WITH untouched vertices; "
                  f"max untouched-vertex degree = {maxd}")
            for g,unt,degs in found[:3]:
                ce=len(critical_edges(g))
                print(f"    untouched verts {unt} degrees {degs}, critE={ce}, edges={sorted(g.edges)}")
        else:
            print(f"  n={n} δ≥6: NO vertex-critical graph with an untouched vertex in {2000} samples")
    print("\nVERDICT: if untouched vertices only occur at LOW degree (and never at δ≥6),")
    print("that's an impossibility constraint (witness needs δ≥6 but δ≥6 ⟹ E* spanning).")
    print("If an untouched vertex at δ≥6 is found, that's the existence lead (forge's test).")


if __name__ == "__main__":
    main()
