#!/usr/bin/env python3
"""
overlap_count.py — empirical test of wall's L3 (overlap counting) for the E944
impossibility direction. (count, E944)

For a 4-vertex-critical graph G, for each edge e build a spanning 4-EDGE-critical
subgraph H_e of G-e (exists iff e is non-critical, i.e. chi(G-e)=4). Record:
  - which edges f lie in H_e
  - multiplicity m(f) = #{ non-critical e : f in H_e }
  - Sigma_e |E(H_e)| over non-critical e
  - test whether the double-count forces a contradiction with "no critical edge".

A spanning 4-edge-critical subgraph H_e of a 4-chromatic graph X=G-e is obtained
by greedily deleting edges of X while chi stays 4, until 4-edge-critical. The
result depends on deletion order; to probe L3 robustly we record the UNION over a
few random orders (an edge f is "avoidable from e" if SOME order excludes it).

Key L3 question: is there an edge f forced into H_e for EVERY non-critical e?
If yes for the witness-hypothetical (all edges non-critical), that f is in every
spanning 4-critical subgraph ⇒ f is critical ⇒ contradiction with no-critical-edge.
We test on real 4-vtx-critical graphs whether 'every edge avoidable' is achievable.
"""
import random
import networkx as nx
from critedge import chromatic_number, is_vertex_critical, critical_edges


def edge_critical_subgraph(X, seed=0):
    """Greedily delete edges of 4-chromatic X while chi stays 4. Returns a
    4-edge-critical spanning subgraph (edge set)."""
    rng = random.Random(seed)
    H = X.copy()
    assert chromatic_number(H) == 4
    edges = list(H.edges())
    rng.shuffle(edges)
    for (u, v) in edges:
        if H.has_edge(u, v):
            H.remove_edge(u, v)
            if chromatic_number(H) < 4:
                H.add_edge(u, v)  # was critical in current H, keep it
    return set(frozenset(e) for e in H.edges())


def analyze(G, name, trials=6):
    chi = chromatic_number(G)
    assert chi == 4 and is_vertex_critical(G, 4), f"{name} not 4-vtx-critical"
    crit = set(frozenset(e) for e in critical_edges(G))
    all_edges = [frozenset(e) for e in G.edges()]
    noncrit = [e for e in all_edges if e not in crit]
    n = G.number_of_nodes()
    print(f"\n=== {name}: n={n} m={len(all_edges)} "
          f"#critical={len(crit)} #non-critical={len(noncrit)}")

    # For each NON-critical edge e, build H_e (spanning 4-edge-critical in G-e).
    # Record for each edge f: in how many H_e it appears (multiplicity), and
    # whether f is EVER avoidable (excluded from some H_e for some e/order).
    mult = {f: 0 for f in all_edges}
    avoidable = {f: False for f in all_edges}  # excluded from at least one H_e
    He_sizes = []
    for e in noncrit:
        X = G.copy(); X.remove_edge(*tuple(e))
        # union over trials of which edges get kept
        kept_union = set()
        for t in range(trials):
            He = edge_critical_subgraph(X, seed=t)
            kept_union |= He
            He_sizes.append(len(He))
        # f avoidable-from-e if f excluded in the smallest He we saw; approx by:
        # an edge f != e that is NOT in kept_union is avoidable from e.
        for f in all_edges:
            if f == e:
                continue
            if f in kept_union:
                mult[f] += 1
            else:
                avoidable[f] = True
        avoidable[e] = True  # e itself excluded from H_e by construction

    # Report
    avg_He = sum(He_sizes) / len(He_sizes) if He_sizes else 0
    print(f"   avg |H_e| over non-critical e (union of {trials} orders): {avg_He:.1f}")
    # Which edges are NEVER avoidable (in every H_e they appear)?
    never_avoidable = [f for f in all_edges if not avoidable[f]]
    print(f"   edges NEVER avoidable from any non-critical e: {len(never_avoidable)}")
    if never_avoidable:
        print(f"      (these are forced into every H_e — would be 'critical-like')")
    # The critical edges should be the ones that are inherently un-removable
    print(f"   critical edges (chi(G-e)=3): {len(crit)} "
          f"— these can't even start an H_e")
    return {"n": n, "m": len(all_edges), "ncrit": len(crit),
            "nnoncrit": len(noncrit), "never_avoidable": len(never_avoidable)}


def main():
    print("L3 overlap-counting empirical probe (count, for wall)")
    print("Goal: does 'every edge avoidable by some spanning 4-edge-critical")
    print("subgraph' ever fail on a real 4-vtx-critical graph? If an edge is")
    print("NEVER avoidable, overlap-counting has teeth.\n")
    results = []
    # C7(1,2)
    G1 = nx.Graph();
    for d in (1,2):
        for i in range(7): G1.add_edge(i,(i+d)%7)
    results.append(analyze(G1, "C7(1,2)"))
    # C13(1,2,5)
    G2 = nx.Graph()
    for d in (1,2,5):
        for i in range(13): G2.add_edge(i,(i+d)%13)
    results.append(analyze(G2, "C13(1,2,5)"))
    # K4 (all edges critical — should show 0 non-critical)
    results.append(analyze(nx.complete_graph(4), "K4"))
    print("\n" + "="*60)
    print("Summary: on these 4-vtx-critical graphs, are critical edges exactly")
    print("the 'never avoidable' ones? (the L3 question)")
    for r in results:
        print(f"   n={r['n']} m={r['m']} crit={r['ncrit']} "
              f"never-avoidable={r['never_avoidable']}")
    print("="*60)


if __name__ == "__main__":
    main()
