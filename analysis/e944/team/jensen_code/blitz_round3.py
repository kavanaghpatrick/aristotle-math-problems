"""
INVENTION BLITZ — jensen lane, ROUND 3. Per verdict: structured (vertex-transitive)
families all fail; pivot to IRREGULAR / ASYMMETRIC dense δ≥6 graphs. These are
genuinely new (not group/circulant): build asymmetry IN by construction.

J6 Twisted circulant-pair: take the verified vertex-critical δ=4 circulant C_n(s1,s2)
   (χ=4, fully critical) and ADD a few asymmetric chords to push δ→6 WITHOUT breaking
   vertex-criticality — does the added density de-criticalize some edges while
   asymmetry preserves vertex-criticality? (This is the J5 sparse-but-vc seed + targeted
   densification, the one combination not yet tried.)
J7 Random δ=6 graph filtered to χ=4, then check vertex-criticality + critical count.
   Pure existence probe in the irregular dense regime (where no structured family lives).
J8 Two C13(1,2,5)-cores cross-linked asymmetrically (the densest known vertex-critical
   object, count's optimum) — glue two copies with a sparse asymmetric bridge set to
   see if cross-links de-criticalize each core's edges while keeping vertex-criticality.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools, random
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def score(G, name, quiet_fail=False):
    if not nx.is_connected(G):
        if not quiet_fail: print(f"{name}: DISCONNECTED");
        return None
    n=G.number_of_nodes(); m=G.number_of_edges()
    chi=chromatic_number(G); dmin=min(d for _,d in G.degree())
    if chi!=4:
        if not quiet_fail: print(f"{name}: n={n} m={m} δ={dmin} χ={chi}")
        return None
    vc=is_vertex_critical(G,4)
    if not vc:
        if not quiet_fail: print(f"{name}: n={n} m={m} δ={dmin} χ=4 vtx-crit=False")
        return None
    ce=critical_edges(G); br=len(list(nx.bridges(G)))
    tag="  *** WITNESS ***" if len(ce)==0 else ""
    print(f"{name}: n={n} m={m} δ={dmin} χ=4 vtx-crit=True #critical={len(ce)}/{m} bridges={br}{tag}")
    return len(ce)


# J6: vertex-critical circulant + asymmetric densifying chords
def J6_twisted(n, base_shifts, n_chords, seed):
    G = nx.circulant_graph(n, base_shifts)
    rng = random.Random(seed)
    nonedges = [(i,j) for i in range(n) for j in range(i+1,n) if not G.has_edge(i,j)]
    rng.shuffle(nonedges)
    added=0
    for (i,j) in nonedges:
        if added>=n_chords: break
        G.add_edge(i,j); added+=1
    return G


# J7: random regular-ish δ>=6 graph filtered to chi=4
def J7_random_dense(n, deg, seed):
    rng = random.Random(seed)
    try:
        G = nx.random_regular_graph(deg, n, seed=seed)
    except Exception:
        return None
    return G


# J8: two cores cross-linked asymmetrically
def J8_crosslink(core_n, core_shifts, n_bridges, seed):
    A = nx.circulant_graph(core_n, core_shifts)
    B = nx.circulant_graph(core_n, core_shifts)
    G = nx.disjoint_union(A, B)  # nodes 0..core_n-1 and core_n..2core_n-1
    rng = random.Random(seed)
    # asymmetric bridges: random a in A to random b in B
    for _ in range(n_bridges):
        a = rng.randrange(core_n); b = core_n + rng.randrange(core_n)
        G.add_edge(a,b)
    return G


if __name__=="__main__":
    print("=== BLITZ ROUND 3 (jensen lane — IRREGULAR/ASYMMETRIC dense) ===")
    print("-- J6 twisted vertex-critical circulant + asymmetric chords --")
    best=None
    for n in (13,14):
        for (bs) in ([1,5],[2,3],[1,2,5]):
            for nc in (1,2,3,4):
                for seed in range(6):
                    r = score(J6_twisted(n,bs,nc,seed), f"J6 C_{n}{bs}+{nc}ch s{seed}", quiet_fail=True)
                    if r is not None and (best is None or r<best[0]):
                        best=(r, n, bs, nc, seed)
    if best:
        print(f"  J6 best vertex-critical χ=4: {best[0]} critical edges at C_{best[1]}{best[2]}+{best[3]}chords seed{best[4]}")
        # reprint it loudly
        score(J6_twisted(best[1],best[2],best[3],best[4]), f"J6 BEST")
    else:
        print("  J6: no χ=4 vertex-critical found among twisted variants")

    print("-- J7 random δ≥6 dense, filtered χ=4 vertex-critical --")
    cnt=0
    for n in (12,13,14):
        for deg in (6,):
            for seed in range(20):
                r = score(J7_random_dense(n,deg,seed), f"J7 n={n} d={deg} s{seed}", quiet_fail=True)
                if r is not None:
                    score(J7_random_dense(n,deg,seed), f"J7 n={n} d={deg} s{seed}")
                    cnt+=1
    if cnt==0: print("  J7: no χ=4 vertex-critical random 6-regular found (n=12,13,14, 60 samples)")

    print("-- J8 two cross-linked cores (asymmetric) --")
    bestg=None
    for cn in (7,):
        for bs in ([1,2],):
            for nb in (2,3,4,5):
                for seed in range(6):
                    r = score(J8_crosslink(cn,bs,nb,seed), f"J8 2xC_{cn}{bs}+{nb}br s{seed}", quiet_fail=True)
                    if r is not None and (bestg is None or r<bestg[0]):
                        bestg=(r,cn,bs,nb,seed)
    if bestg:
        print(f"  J8 best: {bestg[0]} critical edges")
    else:
        print("  J8: no χ=4 vertex-critical found")
