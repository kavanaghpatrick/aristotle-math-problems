#!/usr/bin/env python3
"""
forge_assault_c13.py — orbit-surgery campaign on C13(1,2,5).

C13(1,2,5): 6-regular, χ=4, 4-vertex-critical. Only the difference-1 orbit (the
13-edge Hamilton cycle 0-1-2-...-12-0) is critical; the diff-2 and diff-5 orbits
are redundant (26/39 edges non-critical). It satisfies SkSt Prop 5.1 (δ=6).

GOAL: break vertex-transitivity ON the critical orbit so those 13 diff-1 edges
gain a redundant 4-chromatic obstruction avoiding each of them, WITHOUT (a)
re-creating a critical edge elsewhere and (b) losing vertex-criticality.

SURGERY MOVES (each keeps 6-regularity where possible; verified exactly):
  S1. single-edge swap: remove diff-1 edge (i,i+1), add a chord (i,j) for j not
      adjacent. Pairs of swaps keep degrees balanced.
  S2. twisted reattachment: for one vertex i, replace its two diff-1 edges
      {(i,i-1),(i,i+1)} by a twisted pair to i±t.
  S3. chord addition (degree goes to 7 somewhere; relax regularity): add a chord
      that double-covers a critical edge, then re-prune to vertex-critical.
  S4. 2-swap rewire (edge switching that preserves all degrees): pick two edges
      (a,b),(c,d), replace by (a,c),(b,d) if valid. Classic degree-preserving move.

Score = number of critical edges (lower is better; 0 with vertex-criticality =
WITNESS). Dual-verify every improvement with count's checkers.is_erdos944_k_r1.
"""
import itertools
import random
import networkx as nx
from forge_verify import (is_k_colorable, is_vertex_critical, critical_edges)
import checkers


def circ(n, S):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for i in range(n):
        for s in S:
            G.add_edge(i, (i + s) % n)
    return G


def is_4vc_nx(G):
    if is_k_colorable(G, 3) or not is_k_colorable(G, 4):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def crit_count(G):
    return len(critical_edges(G, 4))


def nx_to_edges_n(G):
    G2 = nx.convert_node_labels_to_integers(G)
    return [tuple(sorted(e)) for e in G2.edges()], G2.number_of_nodes()


def dual_verify_witness(G):
    """Confirm witness with BOTH engines: forge_verify and count's checkers."""
    if not is_4vc_nx(G):
        return False
    if crit_count(G) != 0:
        return False
    edges, n = nx_to_edges_n(G)
    return checkers.is_erdos944_k_r1(edges, n, k=4)


def degree_preserving_2swap(G, rng):
    """Pick 2 edges (a,b),(c,d), rewire to (a,c),(b,d) keeping degrees. Returns H or None."""
    edges = list(G.edges())
    if len(edges) < 2:
        return None
    (a, b), (c, d) = rng.sample(edges, 2)
    if len({a, b, c, d}) < 4:
        return None
    # try the two rewirings
    for (x, y), (u, v) in [((a, c), (b, d)), ((a, d), (b, c))]:
        if G.has_edge(x, y) or G.has_edge(u, v):
            continue
        H = G.copy()
        H.remove_edge(a, b); H.remove_edge(c, d)
        H.add_edge(x, y); H.add_edge(u, v)
        return H
    return None


def campaign(seed_S=(1, 2, 5), n=13, rounds=8000, seed=0):
    rng = random.Random(seed)
    G = circ(n, seed_S)
    assert is_4vc_nx(G), "seed not 4vc"
    base = crit_count(G)
    print(f"seed C{n}{seed_S}: 6-regular, critical_edges={base}", flush=True)
    bestG, best = G.copy(), base
    cur, curc = G.copy(), base
    for it in range(rounds):
        H = degree_preserving_2swap(cur, rng)
        if H is None:
            cur, curc = bestG.copy(), best  # restart from best
            continue
        if not is_4vc_nx(H):
            continue
        hc = crit_count(H)
        # accept if <= current (allow lateral to explore), track best
        if hc <= curc:
            cur, curc = H, hc
            if hc < best:
                bestG, best = H.copy(), hc
                print(f"  it {it}: critical_edges={hc} "
                      f"(degseq {sorted([d for _,d in H.degree()],reverse=True)[:3]}...)",
                      flush=True)
                if hc == 0:
                    if dual_verify_witness(H):
                        print("  *** DUAL-VERIFIED WITNESS ***", flush=True)
                        return bestG, 0, True
                    else:
                        print("  (0 critical but failed dual-verify — bug? keep going)",
                              flush=True)
        # occasional restart to escape plateaus
        if it % 500 == 499:
            cur, curc = bestG.copy(), best
    return bestG, best, False


if __name__ == "__main__":
    import sys
    overall = None
    # multiple seeds + the C13(1,2,5) start, also try other 6-regular near-misses
    starts = [((1, 2, 5), 13), ((1, 2, 5), 16), ((1, 2, 5), 14), ((1, 2, 5), 15)]
    for S, n in starts:
        G0 = circ(n, S)
        if not is_4vc_nx(G0):
            print(f"C{n}{S}: not 4vc, skip", flush=True)
            continue
        for trial in range(3):
            print(f"\n=== Campaign C{n}{S} trial {trial} ===", flush=True)
            G, c, win = campaign(S, n, rounds=4000, seed=trial * 31 + 5)
            if overall is None or c < overall[1]:
                overall = (G.copy(), c, S, n, trial)
            if win:
                break
        if overall and overall[1] == 0:
            break
    G, c, S, n, trial = overall
    print(f"\nBEST: critical_edges={c} from C{n}{S} t{trial} "
          f"n={G.number_of_nodes()} m={G.number_of_edges()}", flush=True)
    edges, nn = nx_to_edges_n(G)
    tag = "WITNESS" if c == 0 and dual_verify_witness(G) else f"best_c{c}"
    with open(f"forge_assault_c13_{tag}.txt", "w") as f:
        f.write(f"# C13-surgery best: n={nn} m={len(edges)} critical_edges={c}\n")
        for u, v in sorted(edges):
            f.write(f"{u} {v}\n")
    print(f"Saved forge_assault_c13_{tag}.txt", flush=True)
