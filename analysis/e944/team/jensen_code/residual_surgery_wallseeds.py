"""
Residual-surgery on wall's WALL-5 plateau seeds (n=19, n=23), per wall's guidance:
- prioritize residual critical edges incident to LOW-DEGREE (3/4/5) vertices,
- prefer ADD moves that RAISE a low-degree endpoint toward δ=6,
- track TOTAL critE (entangle-rewire can relocate criticality), accept only if it DROPS,
- never leave the χ=4 ∧ vertex-critical manifold.
Any sequence reaching critE=0 while vertex-critical = WITNESS → flag instantly.
"""
from __future__ import annotations
import sys, os, json
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def vc4(G):
    return chromatic_number(G) == 4 and is_vertex_critical(G, 4)


def load_seeds(path):
    out = []
    for s in json.load(open(path)):
        G = nx.Graph(); G.add_edges_from(tuple(e) for e in s["edges"])
        out.append((s["label"], G))
    return out


def local_nonedges(G, u, v):
    local = list(set([u, v]) | set(G.neighbors(u)) | set(G.neighbors(v)))
    return [(a, b) for a, b in itertools.combinations(local, 2) if not G.has_edge(a, b)]


def try_descend(G0, verbose=True):
    G = G0.copy()
    base_ce = critical_edges(G)
    base = len(base_ce)
    deg = dict(G.degree())
    # priority: critical edges incident to lowest-degree vertices first
    crit_sorted = sorted(base_ce, key=lambda e: min(deg[e[0]], deg[e[1]]))
    best = None  # (new_count, kind, payload)

    # M1/M3: local adds, prioritizing those that raise a low-degree endpoint
    for (u, v) in crit_sorted:
        cand = local_nonedges(G, u, v)
        # prefer adds touching the lower-degree endpoint
        lo = u if deg[u] <= deg[v] else v
        cand.sort(key=lambda ab: 0 if lo in ab else 1)
        for (a, b) in cand:
            G.add_edge(a, b)
            if vc4(G):
                c = len(critical_edges(G))
                if c < base and (best is None or c < best[0]):
                    best = (c, "add", (a, b))
            G.remove_edge(a, b)
        if best is not None:
            break  # take first improving low-degree-incident edge's best add

    # M2: local 2-swap if no add helped
    if best is None:
        crit_set = set(frozenset(e) for e in base_ce)
        for (u, v) in crit_sorted[:8]:
            adds = local_nonedges(G, u, v)[:10]
            local = set([u, v]) | set(G.neighbors(u)) | set(G.neighbors(v))
            removable = [(a, b) for a, b in G.edges()
                         if a in local and b in local and frozenset((a, b)) not in crit_set]
            for (a, b) in adds:
                G.add_edge(a, b)
                for (c, d) in removable[:10]:
                    if not G.has_edge(c, d):
                        continue
                    G.remove_edge(c, d)
                    if vc4(G):
                        cc = len(critical_edges(G))
                        if cc < base and (best is None or cc < best[0]):
                            best = (cc, "swap", ((a, b), (c, d)))
                    G.add_edge(c, d)
                G.remove_edge(a, b)
            if best is not None:
                break

    if best is None:
        if verbose:
            print(f"  STRICT LOCAL MINIMUM at critE={base}: no prioritized local move reduces it.", flush=True)
        return G0, False
    c, kind, payload = best
    G0 = G0.copy()
    if kind == "add":
        G0.add_edge(*payload)
    else:
        (a, b), (cc, dd) = payload
        G0.add_edge(a, b); G0.remove_edge(cc, dd)
    if verbose:
        print(f"  DESCENT: {kind} {payload} → critE {base}→{c}, δ={min(d for _,d in G0.degree())}", flush=True)
    return G0, True


def run(label, G, max_steps=25):
    print(f"\n=== {label}: n={G.number_of_nodes()} m={G.number_of_edges()} critE={len(critical_edges(G))} δ={min(d for _,d in G.degree())} ===", flush=True)
    assert vc4(G), "seed not vertex-critical!"
    for step in range(max_steps):
        G, improved = try_descend(G)
        cur = len(critical_edges(G))
        if cur == 0:
            print(f"  *** critE=0 AND vertex-critical={is_vertex_critical(G,4)} — WITNESS CANDIDATE! ***", flush=True)
            return G, 0
        if not improved:
            break
    final = len(critical_edges(G))
    print(f"  → final critE={final} m={G.number_of_edges()} δ={min(d for _,d in G.degree())}", flush=True)
    return G, final


if __name__ == "__main__":
    seeds = load_seeds("analysis/e944/team/wall5_plateau_seeds_n19_n23.json")
    results = {}
    for label, G in seeds:
        _, f = run(label, G)
        results[label] = f
    print("\nSUMMARY:", results, flush=True)
    print("(any 0 = WITNESS; otherwise strict local minimum = barrier confirmed at that n)")
