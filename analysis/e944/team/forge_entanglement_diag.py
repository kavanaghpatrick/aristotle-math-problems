#!/usr/bin/env python3
"""
forge_entanglement_diag.py — make jensen's PARALLELISM-vs-ENTANGLEMENT dichotomy
COMPUTATIONAL, as an impossibility/witness diagnostic.

jensen's dichotomy: edge-redundancy (2-edge-connectivity through e) comes 2 ways:
  - SEPARABLE PARALLELISM (rails): e's reroute is a vertex-DISJOINT alternate path
    ⟹ the alternate path's interior vertices are NON-critical. Edge-redundancy bought,
    vertex-criticality LOST. (sparse degree-4 quadrangulations, ladders, parallel chains)
  - ENTANGLEMENT: reroutes for e SHARE vertices with e's neighborhood, no spare rail
    ⟹ vertices stay critical. (dense, G_5,2,2 with 7 reroutes through common nbhd)

A WITNESS needs ENTANGLEMENT at every edge. This diagnostic measures, for each edge
e=(u,v) in a 4-vertex-critical (or k-vc) graph: how "entangled" vs "rail-like" is the
local structure?

PROXY METRICS (computable, no need for the abstract obstruction H_e):
  1. common-neighbor count |N(u)∩N(v)| — entanglement needs shared neighbors (rails
     have NONE: a rail reroute u-a-...-b-v has a,b NOT adjacent to both).
  2. local edge-connectivity λ(u,v) and whether the vertex-disjoint paths between u,v
     pass through N(u)∪N(v) (entangled) or through far-away rails.
  3. "rail index": fraction of internally-vertex-disjoint u-v paths (length≥2) whose
     internal vertices are NOT in N(u)∪N(v) (high = rail-like = bad for witness).

We compute these on: the k=5 witness G_5,2,2 (POSITIVE: should be entangled),
G_5,2,4 (2nd positive), the |E*|=0 k=4 near-misses (cocktail, K(6,2): should be
rail-like / parallel, explaining why they lose vertex-criticality), and the
vertex-critical k=4 hosts (n10 champion, C13).
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, critical_edges


def circ(n, S):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for i in range(n):
        for s in S:
            G.add_edge(i, (i + s) % n)
    return G


def kneser(n, k):
    V = list(itertools.combinations(range(n), k)); G = nx.Graph(); G.add_nodes_from(V)
    for a, b in itertools.combinations(V, 2):
        if not (set(a) & set(b)): G.add_edge(a, b)
    return nx.convert_node_labels_to_integers(G)


def entanglement_metrics(G, name, sample=15):
    """Per-edge: common neighbors, and the 'rail index' proxy."""
    G = nx.convert_node_labels_to_integers(G)
    edges = list(G.edges())
    import random
    rng = random.Random(0)
    if len(edges) > sample:
        edges = rng.sample(edges, sample)
    cn_counts = []
    rail_fracs = []
    for (u, v) in edges:
        Nu = set(G.neighbors(u)) - {v}
        Nv = set(G.neighbors(v)) - {u}
        common = Nu & Nv
        cn_counts.append(len(common))
        # rail index: among vertex-disjoint u-v paths (excluding the direct edge),
        # how many route ENTIRELY outside N(u)∪N(v)? Approx via: remove edge uv, find
        # node-disjoint paths; classify each by whether its internal vertices ⊆ N(u)∪N(v).
        H = G.copy(); H.remove_edge(u, v)
        try:
            # node-disjoint paths between u and v
            paths = list(nx.node_disjoint_paths(H, u, v))
        except Exception:
            paths = []
        if paths:
            local_nbhd = Nu | Nv
            rail = 0
            for p in paths:
                internal = set(p[1:-1])
                # 'rail' = a reroute whose internal vertices avoid the shared/local nbhd
                # (i.e. doesn't pass through u,v's common structure) — a separate track
                if internal and not (internal & common):
                    rail += 1
            rail_fracs.append(rail / len(paths))
        else:
            rail_fracs.append(1.0)
    import statistics
    avg_cn = statistics.mean(cn_counts) if cn_counts else 0
    min_cn = min(cn_counts) if cn_counts else 0
    avg_rail = statistics.mean(rail_fracs) if rail_fracs else 1.0
    print(f"[{name}] sampled {len(edges)} edges: avg common-nbrs/edge={avg_cn:.2f} "
          f"(min={min_cn}); avg rail-fraction={avg_rail:.2f} "
          f"({'ENTANGLED (low rail, shared nbrs)' if avg_rail < 0.5 and min_cn >= 1 else 'RAIL-LIKE / parallel'})",
          flush=True)
    return avg_cn, min_cn, avg_rail


if __name__ == "__main__":
    print("=== jensen entanglement-vs-parallelism diagnostic ===\n", flush=True)
    print("POSITIVE k=5 witnesses (should be ENTANGLED):", flush=True)
    entanglement_metrics(circ(17, {1, 3, 4, 5}), "G_5,2,2 (k=5 witness, δ=8)")
    entanglement_metrics(circ(33, {1, 3, 4, 5, 12, 13, 21}), "G_5,2,4 (k=5 witness, δ=12)")
    print("\n|E*|=0 k=4 near-misses (NOT vertex-critical; should be RAIL-LIKE per jensen):", flush=True)
    entanglement_metrics(nx.complete_multipartite_graph(2, 2, 2, 2), "cocktail K_{2,2,2,2}")
    entanglement_metrics(kneser(6, 2), "K(6,2) Kneser")
    entanglement_metrics(nx.from_graph6_bytes("GCZvv{".encode()), "n8 GCZvv{ (|E*|=0)")
    print("\nVERTEX-CRITICAL k=4 hosts (|E*|>0):", flush=True)
    entanglement_metrics(nx.from_graph6_bytes("ICpdbY{]_".encode()), "n10 champion (|E*|=8)")
    entanglement_metrics(circ(13, {1, 2, 5}), "C13(1,2,5) (|E*|=13)")
