#!/usr/bin/env python3
"""
wall5_pairmove.py — JOINT experiment (count + wall): seed CNT-1 pair-move SA from
WALL-5 edge-addition-descent plateau graphs. (E944 invention blitz)

WALL-5 (wall's primitive): from a 4-vertex-critical seed (Mycielskian), greedily ADD
non-edges, each the one that most reduces #critical-edges WHILE preserving vertex-
criticality, until plateau (≈ n+2 critical edges). Then count's pair-move SA tries to
cross the last gap to (0 critical edges, vertex-critical).

The decisive question: can the pair-move cross from a WALL-5 plateau (already near the
corner, asymmetric Mycielski basin — different from circulants) to a genuine witness?
"""
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
import networkx as nx


def to_graph(G):
    nodes = list(G.nodes()); idx = {x: i for i, x in enumerate(nodes)}
    return Graph(len(nodes), [(idx[a], idx[b]) for a, b in G.edges()])


def is_vertex_critical(g):
    return chi_exact(g.adj, g.n) == 4 and all(g.chi_minus_vertex(v) < 4 for v in range(g.n))

def critical_edges(g):
    return [(a, b) for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4]


def wall5_descend(g, max_adds=40, verbose=True):
    """Greedily add the non-edge that most reduces #critical-edges while keeping
    vertex-critical. Plateau when no addition helps."""
    assert is_vertex_critical(g), "seed must be 4-vertex-critical"
    cur_ce = len(critical_edges(g))
    if verbose: print(f"  WALL-5 start: n={g.n} critE={cur_ce}")
    for step in range(max_adds):
        best = None
        nonedges = [(u, v) for u in range(g.n) for v in range(u+1, g.n) if not g.has(u, v)]
        random.shuffle(nonedges)
        for (u, v) in nonedges:
            g.add(u, v)
            if is_vertex_critical(g):
                ce = len(critical_edges(g))
                if ce < cur_ce and (best is None or ce < best[2]):
                    best = (u, v, ce)
            g.remove(u, v)
            if best and best[2] <= cur_ce - 2:  # good enough this step, take it
                break
        if best is None:
            if verbose: print(f"  WALL-5 plateau at critE={cur_ce} after {step} adds")
            break
        g.add(best[0], best[1]); cur_ce = best[2]
        if verbose: print(f"    +edge {(best[0],best[1])} -> critE={cur_ce}")
    return g, cur_ce


# pair-move SA (from CNT-1, adapted, min-deg-aware)
from count_anneal3 import three_coloring_of

def combined_potential(g):
    chi = chi_exact(g.adj, g.n)
    if chi != 4:
        return 100 + 50*(abs(chi-4)+(5 if chi<4 else 0)), (chi,)
    ncv = sum(1 for v in range(g.n) if g.chi_minus_vertex(v) >= 4)
    ce = len(critical_edges(g))
    return ce*ncv + (ce+ncv), (chi, ncv, ce)  # corner-seeking product+sum

def two_swap(g, rng):
    edges = tuple(g.edges)
    if len(edges) < 2: return ("noop", None)
    for _ in range(20):
        a,b=rng.choice(edges); c,d=rng.choice(edges)
        if len({a,b,c,d})<4: continue
        for e1,e2 in [((a,c),(b,d)),((a,d),(b,c))]:
            if not g.has(*e1) and not g.has(*e2):
                g.remove(a,b); g.remove(c,d); g.add(*e1); g.add(*e2)
                return ("swap",((min(a,b),max(a,b)),(min(c,d),max(c,d)),
                                (min(*e1),max(*e1)),(min(*e2),max(*e2))))
    return ("noop", None)

def pair_move(g, rng):
    chi = chi_exact(g.adj, g.n)
    crit = critical_edges(g) if chi==4 else []
    ncv = [v for v in range(g.n) if g.chi_minus_vertex(v) >= 4] if chi==4 else []
    if crit and ncv:
        e = rng.choice(crit); w = rng.choice(ncv)
        col = three_coloring_of(g, exclude_edge=e)
        if col is not None:
            same=[x for x in range(g.n) if x!=w and col[x]==col[w] and not g.has(w,x)]
            wn=[x for x in range(g.n) if g.has(w,x)]
            if same and wn:
                x=rng.choice(same); p=rng.choice(wn)
                xn=[y for y in range(g.n) if g.has(x,y) and y not in (w,p)]
                if xn:
                    q=rng.choice(xn)
                    if not g.has(p,q) and len({w,x,p,q})==4:
                        g.remove(w,p); g.remove(x,q); g.add(w,x); g.add(p,q)
                        return ("swap",((min(w,p),max(w,p)),(min(x,q),max(x,q)),
                                        (min(w,x),max(w,x)),(min(p,q),max(p,q))))
    return two_swap(g, rng)

def undo(g, mv):
    if mv[0]!="swap": return
    o1,o2,n1,n2=mv[1]; g.remove(*n1); g.remove(*n2); g.add(*o1); g.add(*o2)

def pairmove_sa(g0, rng, iters=8000, tag=""):
    g=g0.copy(); cur,info=combined_potential(g); best=cur; bg=g.copy(); bi=info
    T=4.0; decay=(0.02/4.0)**(1/iters)
    for it in range(iters):
        mv=pair_move(g,rng)
        if mv[0]=="noop": T*=decay; continue
        new,ninfo=combined_potential(g); d=new-cur
        if d<=0 or rng.random()<math.exp(-d/max(T,1e-9)):
            cur,info=new,ninfo
            if new<best:
                best=new; bg=g.copy(); bi=ninfo
                if len(bi)==3 and bi[1]==0 and bi[2]==0:
                    return ("WITNESS", bg, bi, it)
        else: undo(g,mv)
        T*=decay
    return ("done", bg, bi, -1)


def main():
    rng = random.Random(2718)
    random.seed(2718)
    print("=== JOINT WALL-5 descend + count pair-move cross (E944) ===\n")
    # build Mycielskian seeds independently (wall used Myc(C7) n=15, Grotzsch=Myc(C5) n=11)
    seeds = {"Myc(C5)=Grotzsch-n11": to_graph(nx.mycielskian(nx.cycle_graph(5))),
             "Myc(C7)-n15": to_graph(nx.mycielskian(nx.cycle_graph(7)))}
    for name, g in seeds.items():
        print(f"--- seed {name}: n={g.n} chi={chi_exact(g.adj,g.n)} "
              f"vtx-critical={is_vertex_critical(g)} critE={len(critical_edges(g))}")
        if not is_vertex_critical(g):
            print("    (not vertex-critical, skip)"); continue
        # WALL-5 descend
        gd, ce = wall5_descend(g.copy())
        ncv = sum(1 for v in range(gd.n) if gd.chi_minus_vertex(v)>=4)
        mind = min(gd.degree(v) for v in range(gd.n))
        print(f"  WALL-5 plateau: n={gd.n} critE={ce} ncV={ncv} min-deg={mind}")
        # count pair-move cross attempt
        status, bg, bi, it = pairmove_sa(gd, rng, iters=6000, tag=name)
        print(f"  pair-move from plateau: status={status} best info(chi,ncV,critE)={bi}")
        if status == "WITNESS":
            print(f"  *** WITNESS!! n={bg.n} edges={sorted(bg.edges)} — DUAL-VERIFY ***")
        else:
            print(f"  -> did NOT cross to (0,0); best Φ-info={bi}")
        print()
    print("VERDICT: if no (0,0) reached from WALL-5 plateaus (closer to corner than")
    print("circulants, asymmetric Mycielski basin), strong COMBINED impossibility intel.")


if __name__ == "__main__":
    main()
