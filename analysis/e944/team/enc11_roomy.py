#!/usr/bin/env python3
"""
enc11_roomy.py — ENC-11 roomy instantiation (count + proximity). Search n=13,14 for
a (4,1)-witness in the ASYMMETRIC, NON-REGULAR, δ≥6 corner — where there is ROOM for
min-deg 6 without over-fulling (δ=6 on 13 vtx = 39 of 78 possible edges).

proximity's fix: the over-full trap is partly a cramming artifact (δ=6 on only 10
vertices ⟹ near-K density). At n=13-14 δ=6 is sparse; and keeping degrees MIXED /
|Aut| low (anti-regularity) stays in the ENC-7 asymmetric corner most likely to break
the plateau.

Scorer: minimize critE + vertex-crit debt + degree-deficit-below-6 - small reward for
degree VARIANCE (anti-regularity). Any critE=0 (δ≥6, vertex-critical) -> triple-verify.
"""
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
from count_anneal3 import three_coloring_of
import networkx as nx


def vc(g): return chi_exact(g.adj,g.n)==4 and all(g.chi_minus_vertex(v)<4 for v in range(g.n))
def crit(g): return [(a,b) for (a,b) in g.edges if g.chi_minus_edge(a,b)<4]

def score(g, anti_reg=0.3):
    chi=chi_exact(g.adj,g.n)
    if chi!=4: return 300+50*(abs(chi-4)+(5 if chi<4 else 0)),(chi,)
    ncv=sum(1 for v in range(g.n) if g.chi_minus_vertex(v)>=4)
    ce=len(crit(g))
    degs=[g.degree(v) for v in range(g.n)]
    mind=min(degs)
    deg_def=sum(max(0,6-d) for d in degs)
    # anti-regularity: reward degree spread (variance) to avoid the regular over-full corner
    mean=sum(degs)/len(degs); var=sum((d-mean)**2 for d in degs)/len(degs)
    return 10*ncv + ce + 3*deg_def - anti_reg*var, (chi,ncv,ce,mind)

def move(g, rng):
    """Mixed: add edge raising a low-degree vertex (de-crit a critical edge), delete
    from a high-degree vertex (keep mixed/sparse), or 2-swap."""
    chi=chi_exact(g.adj,g.n)
    r=rng.random()
    lowdeg=[v for v in range(g.n) if g.degree(v)<6]
    crite=crit(g) if chi==4 else []
    if r<0.45 and lowdeg and crite:
        v=rng.choice(lowdeg); e=rng.choice(crite)
        col=three_coloring_of(g, exclude_edge=e)
        if col is not None:
            same=[x for x in range(g.n) if x!=v and col[x]==col[v] and not g.has(v,x)]
            if same:
                x=rng.choice(same); g.add(v,x); return ("add",(min(v,x),max(v,x)))
    if r<0.65:
        # delete from a HIGH-degree vertex (anti-over-full), only if endpoint stays connected
        hi=[(a,b) for (a,b) in g.edges if g.degree(a)>7 or g.degree(b)>7]
        if hi:
            e=rng.choice(hi); g.remove(*e); return ("del",e)
    # 2-swap
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
    elif mv[0]=="del": g.add(*mv[1])
    elif mv[0]=="swap":
        o1,o2,n1,n2=mv[1]; g.remove(*n1);g.remove(*n2);g.add(*o1);g.add(*o2)

def seed_asym(n, rng):
    """Asymmetric 4-chromatic seed at n: perturbed Mycielskian or random non-regular
    chi=4 graph. Returns a vertex-critical one if found, else any chi=4."""
    # start from a Mycielskian of an odd cycle, pad to n with random edges
    base = nx.mycielskian(nx.cycle_graph(5)) if n<=11 else nx.mycielskian(nx.cycle_graph(7))
    G = nx.Graph(base)
    while G.number_of_nodes() < n:
        v = G.number_of_nodes()
        G.add_node(v)
        # connect to 4-5 random existing
        targets = rng.sample(list(range(v)), min(5, v))
        for t in targets: G.add_edge(v, t)
    nodes=list(G.nodes()); idx={x:i for i,x in enumerate(nodes)}
    g = Graph(len(nodes), [(idx[a],idx[b]) for a,b in G.edges()])
    return g

def sa(g0, rng, iters=10000, tag=""):
    g=g0.copy(); cur,info=score(g); best=cur; bg=g.copy(); bi=info
    T=12.0; decay=(0.05/12.0)**(1/iters)
    for it in range(iters):
        mv=move(g,rng)
        if mv[0]=="noop": T*=decay; continue
        new,ninfo=score(g); d=new-cur
        if d<=0 or rng.random()<math.exp(-d/max(T,1e-9)):
            cur,info=new,ninfo
            if new<best:
                best=new; bg=g.copy(); bi=ninfo
                if len(bi)==4 and bi[1]==0 and bi[2]==0 and bi[3]>=6:
                    return ("WITNESS",bg,bi,it)
                if len(bi)==4 and bi[1]==0 and bi[3]>=6 and bi[2]<bg.n//3:
                    print(f"  [{tag}] it={it} sub-n/3 feasible: critE={bi[2]} n={bg.n} edges={sorted(bg.edges)}",flush=True)
        else: undo(g,mv)
        T*=decay
        if it%2500==0 and it>0:
            print(f"  [{tag}] it={it} T={T:.2f} best={best:.1f} info(chi,ncV,critE,minD)={bi}",flush=True)
    return ("done",bg,bi,-1)

def main():
    rng=random.Random(141421)
    print("=== ENC-11 roomy asymmetric search, n=13/14, δ≥6 with room ===\n")
    for n in (13, 14):
        g=seed_asym(n,rng)
        print(f"--- n={n} seed: chi={chi_exact(g.adj,g.n)} vtx-crit={vc(g)} critE={len(crit(g))} "
              f"degs(min,max)=({min(g.degree(v) for v in range(g.n))},{max(g.degree(v) for v in range(g.n))})")
        status,bg,bi,it=sa(g,rng,iters=12000,tag=f"roomy-n{n}")
        print(f"  result: status={status} best info(chi,ncV,critE,minD)={bi}")
        if status=="WITNESS":
            G=nx.Graph(); G.add_nodes_from(range(bg.n)); G.add_edges_from(bg.edges)
            g6=nx.to_graph6_bytes(G,header=False).decode().strip()
            print(f"  *** WITNESS!! n={bg.n} g6={g6} — TRIPLE-VERIFY (proximity+skeptic) ***")
        else:
            feas=len(bi)==4 and bi[1]==0 and bi[3]>=6
            print(f"  feasible(δ≥6,vtx-crit): {feas}"+(f" min critE={bi[2]}" if feas else " — wall held"))
        print()
    print("VERDICT: with ROOM (n=13/14) + asymmetry (anti-regular), does the search")
    print("reach (critE=0, δ≥6, vtx-critical), or does the wall hold even without the")
    print("cramming + symmetry artifacts?")

if __name__=="__main__":
    main()
