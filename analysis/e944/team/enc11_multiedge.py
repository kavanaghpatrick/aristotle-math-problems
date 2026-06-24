#!/usr/bin/env python3
"""
enc11_multiedge.py — MULTI-EDGE coordinated moves (proximity's ENC-11 lever) from
forge's n=10 non-circulant champion. (count + proximity, E944 blitz)

proximity: single-edge moves are UNIVERSALLY trapped (circulant C13 AND forge's
n=10 champ both pinned). The untested lever is MULTI-edge granularity: add a BATCH
of k edges at once (coordinated), then re-settle vertex-criticality. Single-move
traps don't preclude coordinated escapes.

Seed: forge n=10 champion g6 ICpdbY{]_ (8 critical edges, 4-vtx-critical, min-deg 4).
Goal: reach critE < 8 with min-deg>=6 AND vertex-critical. Any such hit -> triple-verify.
"""
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
import networkx as nx


def to_graph(G):
    nodes=list(G.nodes()); idx={x:i for i,x in enumerate(nodes)}
    return Graph(len(nodes), [(idx[a],idx[b]) for a,b in G.edges()])

def vc(g): return chi_exact(g.adj,g.n)==4 and all(g.chi_minus_vertex(v)<4 for v in range(g.n))
def crit(g): return [(a,b) for (a,b) in g.edges if g.chi_minus_edge(a,b)<4]

def score(g):
    chi=chi_exact(g.adj,g.n)
    if chi!=4: return 200+50*(abs(chi-4)+(5 if chi<4 else 0)),(chi,)
    ncv=sum(1 for v in range(g.n) if g.chi_minus_vertex(v)>=4)
    ce=len(crit(g))
    mind=min(g.degree(v) for v in range(g.n))
    pen=0 if mind>=6 else 8*(6-mind)
    return 10*ncv + ce + pen, (chi,ncv,ce,mind)

def multiedge_add(g, rng, k):
    """Add k edges at once, biased to (a) raise low-degree vertices, (b) be redundant
    (endpoints already share neighbors). Returns list of added edges (for undo)."""
    added=[]
    for _ in range(k):
        # prefer endpoints with degree<6 and >=1 common neighbor (redundancy)
        cands=[]
        for u in range(g.n):
            for v in range(u+1,g.n):
                if g.has(u,v): continue
                cn=sum(1 for w in range(g.n) if g.has(u,w) and g.has(v,w))
                lowdeg = (g.degree(u)<6) + (g.degree(v)<6)
                cands.append((lowdeg+ (1 if cn>=1 else 0), cn, u, v))
        if not cands: break
        cands.sort(reverse=True)
        # pick among top candidates randomly
        top=cands[:max(3,len(cands)//10)]
        _,_,u,v=rng.choice(top)
        g.add(u,v); added.append((u,v))
    return added

def multiedge_del(g, rng, k):
    """Delete k edges at once (to control density / restore vertex-criticality),
    only deleting from high-degree vertices."""
    removed=[]
    for _ in range(k):
        edges=[e for e in g.edges if g.degree(e[0])>6 and g.degree(e[1])>6]
        if not edges: break
        e=rng.choice(edges); g.remove(*e); removed.append(e)
    return removed

def sa_multiedge(g0, rng, iters=6000, tag=""):
    g=g0.copy(); cur,info=score(g); best=cur; bg=g.copy(); bi=info
    T=8.0; decay=(0.05/8.0)**(1/iters)
    for it in range(iters):
        # multi-edge coordinated move: batch add or add+del
        k=rng.randint(1,4)
        if rng.random()<0.6:
            mv=("add", multiedge_add(g,rng,k))
        else:
            mv=("del", multiedge_del(g,rng,k))
        if not mv[1]:
            T*=decay; continue
        new,ninfo=score(g); d=new-cur
        if d<=0 or rng.random()<math.exp(-d/max(T,1e-9)):
            cur,info=new,ninfo
            if new<best:
                best=new; bg=g.copy(); bi=ninfo
                if len(bi)==4 and bi[1]==0 and bi[2]==0 and bi[3]>=6:
                    return ("WITNESS",bg,bi,it)
                if len(bi)==4 and bi[1]==0 and bi[3]>=6 and bi[2]<8:
                    print(f"  [{tag}] it={it} sub-8 feasible: info={bi} edges={sorted(bg.edges)}",flush=True)
        else:
            # undo
            if mv[0]=="add":
                for e in mv[1]: g.remove(*e)
            else:
                for e in mv[1]: g.add(*e)
        T*=decay
        if it%2000==0 and it>0:
            print(f"  [{tag}] it={it} T={T:.2f} best={best} info={bi}",flush=True)
    return ("done",bg,bi,-1)


def main():
    rng=random.Random(11211)
    print("=== ENC-11 multi-edge coordinated moves from forge n=10 champion ===\n")
    G=nx.from_graph6_bytes("ICpdbY{]_".encode())
    g=to_graph(G)
    print(f"forge champion: n={g.n} chi={chi_exact(g.adj,g.n)} vtx-critical={vc(g)} "
          f"critE={len(crit(g))} min-deg={min(g.degree(v) for v in range(g.n))}")
    status,bg,bi,it=sa_multiedge(g,rng,iters=8000,tag="forge-n10")
    print(f"\nresult: status={status} best info(chi,ncV,critE,minD)={bi}")
    if status=="WITNESS":
        print(f"*** WITNESS!! n={bg.n} g6 candidate edges={sorted(bg.edges)} — TRIPLE-VERIFY ***")
    else:
        feas = (len(bi)==4 and bi[1]==0 and bi[3]>=6)
        print(f"  feasible-and-vertex-critical reached: {feas}; "
              f"{'critE='+str(bi[2]) if feas else 'never simultaneously feasible+vtx-critical'}")
    print("\nVERDICT: did multi-edge coordination cross where single moves are trapped?")


if __name__=="__main__":
    main()
