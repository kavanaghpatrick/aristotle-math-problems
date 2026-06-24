"""
Obstruction-family analysis (jensen, co-write with forge).

For a NON-critical edge e=uv of a 4-vertex-critical G: G−e is 4-chromatic, so it
contains a (spanning) 4-edge-critical subgraph H_e with e ∉ H_e. We extract a
minimal such obstruction and measure whether u,v are 2-EDGE-CONNECTED within H_e
(joined by a cycle in H_e, i.e. e's would-be position is not a bridge of H_e+e).

The construction-side lemma to test: a witness needs every non-critical e to have
an H_e that is 2-edge-connected through e (u,v in a common cycle of H_e) AND
vertex-fragile (some vertex deletion makes H_e 3-colorable). Tree-like / bridge-ful
H_e (u,v a cut pair) is the J–S failure mode.

*** RESULT (2026-06-10): THIS LEMMA IS FALSE — the discriminator does NOT work. ***
Verified below: the k=5 WITNESS G_{5,2,2} has CUT-PAIR (tree-like) minimal H_e (a
non-spanning K4 not even containing u,v), while NON-witnesses (C13(1,2,5), J–S) have
2-edge-connected minimal H_e. OPPOSITE of the hypothesis. Root cause: edge-redundancy
is witnessed by a possibly NON-SPANNING small obstruction (K4-minor suffices), so
"2-edge-connectivity of u,v within the minimal H_e" is ill-defined / arbitrary — the
minimal obstruction need not contain u,v at all. My earlier "bridge ⟹ fail" result was
J–S-TRANSFER-PATH-specific (a whole-graph bridge in that construction), NOT a general
per-edge invariant. Discriminator DROPPED. Kept here as a documented dead end so nobody
re-derives it. The sound discriminators remain: wall's SPANNING-obstruction lemma
(vertex-criticality) + gallai's P(G−e,3) (edge-redundancy) — different obstruction
families, not unifiable via per-edge 2-edge-connectivity.

We extract H_e by greedily deleting edges of G−e while staying 4-chromatic
(⟹ edge-critical), then check u,v's edge-connectivity within H_e.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import networkx as nx
from harness import chromatic_number, critical_edges, is_vertex_critical


def minimal_obstruction(G, avoid_e):
    """Greedily delete edges from G (keeping χ≥4), never deleting avoid_e's... e is
    already absent. Returns a 4-edge-critical spanning subgraph H (every edge
    critical in H) that is 4-chromatic and avoids avoid_e."""
    H = G.copy()
    assert chromatic_number(H) >= 4
    changed = True
    while changed:
        changed = False
        for (a, b) in list(H.edges()):
            H.remove_edge(a, b)
            if chromatic_number(H) >= 4:
                changed = True
                break
            else:
                H.add_edge(a, b)
    return H


def uv_2edge_connected_in(H, u, v):
    """Are u,v joined by a cycle in H (⟺ 2 edge-disjoint u-v paths ⟺ adding e=uv
    makes e a non-bridge)? Use edge-connectivity local value ≥2 (if both present)."""
    if u not in H or v not in H:
        return None
    try:
        k = nx.edge_connectivity(H, u, v)
    except Exception:
        k = 0
    return k  # ≥2 means 2-edge-connected through the uv position


def analyze(G, name, max_edges=8):
    chi = chromatic_number(G)
    ce = set(frozenset(e) for e in critical_edges(G))
    noncrit = [e for e in G.edges() if frozenset(e) not in ce]
    print(f"\n=== {name}: n={G.number_of_nodes()} χ={chi} |E*|={len(ce)} non-critical={len(noncrit)} ===", flush=True)
    if not noncrit:
        print("  (no non-critical edges — every edge critical, no H_e to analyze)")
        return
    results = []
    for e in noncrit[:max_edges]:
        u, v = e
        Ge = G.copy(); Ge.remove_edge(u, v)
        H = minimal_obstruction(Ge, e)
        k = uv_2edge_connected_in(H, u, v)
        spanning = (H.number_of_nodes() == G.number_of_nodes()) and (H.subgraph([n for n in H if H.degree(n) > 0]).number_of_nodes())
        results.append(k)
        print(f"  non-crit e={e}: H_e has {H.number_of_edges()} edges, "
              f"edge-conn(u,v in H_e)={k} ({'2-edge-conn THROUGH e (entangled)' if (k and k>=2) else 'u,v a CUT pair (bridge-ful/tree-like)'})", flush=True)
    if results:
        ent = sum(1 for k in results if k and k >= 2)
        print(f"  SUMMARY: {ent}/{len(results)} sampled non-critical edges have 2-edge-connected (entangled) H_e", flush=True)


if __name__ == "__main__":
    # Positive case: k=5 witness G_{5,2,2} (ALL edges non-critical)
    from circulant_analysis import build_Gkmq
    G5, _, _ = build_Gkmq(5, 2, 2)
    analyze(G5, "G_{5,2,2} k=5 WITNESS (all non-critical)", max_edges=6)

    # C13(1,2,5): 4vc, |E*|=13, 26 non-critical
    analyze(nx.circulant_graph(13, [1, 2, 5]), "C13(1,2,5) 4vc δ=6", max_edges=6)

    # J–S gadget: non-critical edges = B's tripartite edges
    from jensen_siggers import build_Hprime, four_critical_subgraph
    Hp, SG, B2, Gg = build_Hprime(2)
    H = four_critical_subgraph(Hp)
    analyze(H, "J–S H(m=2) (non-critical = B's edges)", max_edges=6)
