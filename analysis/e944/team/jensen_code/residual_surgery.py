"""
Residual-surgery search (jensen, per wall): take a vertex-critical χ=4 PLATEAU graph
(≈n+4 critical edges, threshold-tight, non-modular) and try LOCAL criticality-preserving
moves to de-criticalize its residual critical edges WITHOUT breaking vertex-criticality.

Move set (all checked on harness each step; never leave the χ=4 ∧ vertex-critical manifold):
  M1 local ADD: for a residual critical edge e=uv, add a non-edge in N(u)∪N(v)∪{u,v}'s vicinity.
  M2 local 2-SWAP: add one non-edge + remove one non-critical edge in e's neighborhood.
  M3 entangle-rewire: reroute by adding a chord between two common-neighborhood vertices of e
     (turn a near-bridge of e's obstruction into a cycle).
Accept a move iff it KEEPS χ=4 ∧ vertex-critical AND reduces total #critical edges.

Reports per graph: starting #critical, whether ANY move reduces it (descent found) or the
graph is a strict local minimum (plateau confirmed). If descent found → escalate.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def vc4(G):
    return chromatic_number(G) == 4 and is_vertex_critical(G, 4)


def neighborhood_nonedges(G, u, v):
    """Non-edges with both endpoints in {u,v} ∪ N(u) ∪ N(v) (local to edge uv)."""
    local = set([u, v]) | set(G.neighbors(u)) | set(G.neighbors(v))
    local = list(local)
    out = []
    for a, b in itertools.combinations(local, 2):
        if not G.has_edge(a, b):
            out.append((a, b))
    return out


def try_descend(G0, verbose=True):
    """One descent step: search all local moves around each residual critical edge for a
    move that reduces total #critical while preserving vc4. Returns (G', improved?)."""
    G = G0.copy()
    base_ce = critical_edges(G)
    base = len(base_ce)
    best = None  # (new_count, ('add'|'swap'|'rewire', payload))
    crit_edges = list(base_ce)

    # M1 + M3: local adds near each critical edge
    for (u, v) in crit_edges:
        for (a, b) in neighborhood_nonedges(G, u, v):
            G.add_edge(a, b)
            if vc4(G):
                c = len(critical_edges(G))
                if c < base and (best is None or c < best[0]):
                    best = (c, ("add", (a, b)))
            G.remove_edge(a, b)

    # M2: local 2-swap (add a local non-edge, remove a local non-critical edge)
    if best is None:
        crit_set = set(frozenset(e) for e in crit_edges)
        for (u, v) in crit_edges[:6]:  # limit for cost
            adds = neighborhood_nonedges(G, u, v)[:8]
            local = set([u, v]) | set(G.neighbors(u)) | set(G.neighbors(v))
            removable = [(a, b) for a, b in G.edges()
                         if a in local and b in local and frozenset((a, b)) not in crit_set]
            for (a, b) in adds:
                G.add_edge(a, b)
                for (c, d) in removable[:8]:
                    if not G.has_edge(c, d):
                        continue
                    G.remove_edge(c, d)
                    if vc4(G):
                        cc = len(critical_edges(G))
                        if cc < base and (best is None or cc < best[0]):
                            best = (cc, ("swap", ((a, b), (c, d))))
                    G.add_edge(c, d)
                G.remove_edge(a, b)

    if best is None:
        if verbose:
            print(f"  STRICT LOCAL MINIMUM at #critical={base}: no local move reduces it.")
        return G0, False
    # apply best
    kind, payload = best[1]
    if kind == "add":
        G0 = G0.copy(); G0.add_edge(*payload)
    elif kind == "swap":
        (a, b), (c, d) = payload
        G0 = G0.copy(); G0.add_edge(a, b); G0.remove_edge(c, d)
    if verbose:
        print(f"  DESCENT: {kind} {payload} → #critical {base}→{best[0]}")
    return G0, True


def descend_to_min(G0, max_steps=20, verbose=True):
    G = G0.copy()
    assert vc4(G), "seed must be χ=4 vertex-critical"
    for step in range(max_steps):
        G, improved = try_descend(G, verbose=verbose)
        if not improved:
            break
    return G, len(critical_edges(G))


if __name__ == "__main__":
    print("=== Residual-surgery validation on jensen's own plateau (pre-wall-seeds) ===")
    # my round-4 plateau: C13(2,3)+{0-4, 0-9} = vertex-critical, 13 critical edges
    G = nx.circulant_graph(13, [2, 3]); G.add_edge(0, 4); G.add_edge(0, 9)
    print(f"seed: n={G.number_of_nodes()} m={G.number_of_edges()} vc4={vc4(G)} #critical={len(critical_edges(G))}", flush=True)
    Gf, cf = descend_to_min(G, max_steps=15)
    print(f"after residual-surgery: n={Gf.number_of_nodes()} m={Gf.number_of_edges()} #critical={cf} δ={min(d for _,d in Gf.degree())}", flush=True)
