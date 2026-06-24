#!/usr/bin/env python3
"""
wall5_seeds_cross.py — pair-move cross-attempt from wall's DELIVERED WALL-5 plateau
seeds, with DEGREE-LIFTING bias (count + wall, E944 blitz).

wall's caveat (gallai δ≥6 thm): both seeds have deg-3/4 vertices, and a deg-3 vertex
FORCES its 3 incident edges critical. So part of the critical-count is structural,
unremovable without raising those degrees. The move must RAISE min-degree toward 6
(eliminate deg-3/4 vertices) AS it reduces critical-count. The hard frontier:
δ→6 AND vertex-critical AND low-crit simultaneously.

Any (critE=0, vertex-critical, δ≥6) hit -> triple-verify (critedge + checkers + skeptic).
"""
import sys, os, json, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
from count_anneal3 import three_coloring_of


def vc(g): return chi_exact(g.adj,g.n)==4 and all(g.chi_minus_vertex(v)<4 for v in range(g.n))
def crit(g): return [(a,b) for (a,b) in g.edges if g.chi_minus_edge(a,b)<4]

def score(g):
    chi=chi_exact(g.adj,g.n)
    if chi!=4: return 300+50*(abs(chi-4)+(5 if chi<4 else 0)),(chi,)
    ncv=sum(1 for v in range(g.n) if g.chi_minus_vertex(v)>=4)
    ce=len(crit(g))
    degs=[g.degree(v) for v in range(g.n)]
    mind=min(degs)
    # strong degree-lift term: penalize EVERY vertex below 6 (sum of deficits)
    deg_def=sum(max(0,6-dd) for dd in degs)
    return 10*ncv + ce + 3*deg_def, (chi,ncv,ce,mind,deg_def)

def lift_or_pair_move(g, rng):
    """Prioritize raising a low-degree vertex (add edge from it to a same-color vertex
    in a 3-coloring of G-e for a critical e, killing the edge's criticality AND
    lifting degree). Else degree-preserving 2-swap."""
    chi=chi_exact(g.adj,g.n)
    lowdeg=[v for v in range(g.n) if g.degree(v)<6]
    crite=crit(g) if chi==4 else []
    if lowdeg and crite and rng.random()<0.7:
        v=rng.choice(lowdeg)
        e=rng.choice(crite)
        col=three_coloring_of(g, exclude_edge=e)
        if col is not None:
            # add edge from v to a same-colored non-neighbor (lifts deg(v), may de-crit e)
            same=[x for x in range(g.n) if x!=v and col[x]==col[v] and not g.has(v,x)]
            if same:
                x=rng.choice(same); g.add(v,x); return ("add",(min(v,x),max(v,x)))
    # 2-swap fallback
    edges=tuple(g.edges)
    if len(edges)>=2:
        for _ in range(15):
            a,b=rng.choice(edges); c,d=rng.choice(edges)
            if len({a,b,c,d})<4: continue
            for e1,e2 in [((a,c),(b,d)),((a,d),(b,c))]:
                if not g.has(*e1) and not g.has(*e2):
                    g.remove(a,b);g.remove(c,d);g.add(*e1);g.add(*e2)
                    return ("swap",((min(a,b),max(a,b)),(min(c,d),max(c,d)),
                                    (min(*e1),max(*e1)),(min(*e2),max(*e2))))
    return ("noop",None)

def undo(g,mv):
    if mv[0]=="add": g.remove(*mv[1])
    elif mv[0]=="swap":
        o1,o2,n1,n2=mv[1]; g.remove(*n1);g.remove(*n2);g.add(*o1);g.add(*o2)

def sa(g0, rng, iters=8000, tag=""):
    g=g0.copy(); cur,info=score(g); best=cur; bg=g.copy(); bi=info
    T=10.0; decay=(0.05/10.0)**(1/iters)
    for it in range(iters):
        mv=lift_or_pair_move(g,rng)
        if mv[0]=="noop": T*=decay; continue
        new,ninfo=score(g); d=new-cur
        if d<=0 or rng.random()<math.exp(-d/max(T,1e-9)):
            cur,info=new,ninfo
            if new<best:
                best=new; bg=g.copy(); bi=ninfo
                if len(bi)==5 and bi[1]==0 and bi[2]==0 and bi[3]>=6:
                    return ("WITNESS",bg,bi,it)
                # report any feasible (δ≥6, vtx-critical) low-crit
                if len(bi)==5 and bi[1]==0 and bi[3]>=6:
                    print(f"  [{tag}] it={it} FEASIBLE δ≥6 vtx-crit: critE={bi[2]} edges={sorted(bg.edges)}",flush=True)
        else: undo(g,mv)
        T*=decay
        if it%2000==0 and it>0:
            print(f"  [{tag}] it={it} T={T:.2f} best={best} info(chi,ncV,critE,minD,degDef)={bi}",flush=True)
    return ("done",bg,bi,-1)

def main():
    rng=random.Random(31459)
    print("=== pair-move (degree-lifting) from wall's WALL-5 plateau seeds ===\n")
    seeds=json.load(open(os.path.join(os.path.dirname(__file__),'wall5_plateau_seeds.json')))
    for s in seeds:
        g=Graph(s['n'], [tuple(e) for e in s['edges']])
        print(f"--- {s['label']}: n={g.n} critE={len(crit(g))} min-deg={min(g.degree(v) for v in range(g.n))} vtx-crit={vc(g)}")
        status,bg,bi,it=sa(g,rng,iters=10000,tag=s['label'])
        print(f"  result: status={status} best info(chi,ncV,critE,minD,degDef)={bi}")
        if status=="WITNESS":
            import networkx as nx
            G=nx.Graph(); G.add_nodes_from(range(bg.n)); G.add_edges_from(bg.edges)
            g6=nx.to_graph6_bytes(G,header=False).decode().strip()
            print(f"  *** WITNESS!! n={bg.n} g6={g6} edges={sorted(bg.edges)} — TRIPLE-VERIFY NOW ***")
        else:
            feas = len(bi)==5 and bi[1]==0 and bi[3]>=6
            print(f"  feasible(δ≥6,vtx-crit) reached: {feas}"
                  + (f", min critE there={bi[2]}" if feas else " — never lifted to δ≥6 while vtx-critical"))
        print()
    print("VERDICT: did degree-lifting pair-move cross the δ→6 frontier to a witness?")

if __name__=="__main__":
    main()
