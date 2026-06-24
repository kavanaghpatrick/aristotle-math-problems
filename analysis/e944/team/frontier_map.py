#!/usr/bin/env python3
"""
frontier_map.py — map the (ncV, critE) Pareto frontier per δ-target ∈ {4,5,6}.
(count + wall, E944) The decisive question: does the frontier between vertex-
criticality (ncV=0) and no-critical-edge (critE=0) ever touch (0,0) at any δ-target?

For each δ-target and n, sweep Lagrangian weight λ on ncV (critE weight = 1), enforce
δ≥target via degree-deficit penalty, SA from a 4-chromatic seed. Record best (ncV,critE)
reached at each λ. Pareto frontier = lower-left envelope. wall's prediction: convex,
origin-avoiding, closest approach ~δ=5.
"""
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
from count_anneal3 import three_coloring_of
import networkx as nx


def critE(g): return sum(1 for (a,b) in g.edges if g.chi_minus_edge(a,b)<4)
def ncV(g): return sum(1 for v in range(g.n) if g.chi_minus_vertex(v)>=4)

def state(g):
    chi=chi_exact(g.adj,g.n)
    if chi!=4: return None
    return (ncV(g), critE(g), min(g.degree(v) for v in range(g.n)))

def score(g, lam, dtarget):
    chi=chi_exact(g.adj,g.n)
    if chi!=4: return 500+50*(abs(chi-4)+(5 if chi<4 else 0))
    nc=ncV(g); ce=critE(g)
    degdef=sum(max(0,dtarget-g.degree(v)) for v in range(g.n))
    # also discourage going far ABOVE dtarget (keep near the target degree)
    over=sum(max(0,g.degree(v)-(dtarget+2)) for v in range(g.n))
    return lam*nc + ce + 5*degdef + 0.5*over

def move(g, rng, dtarget):
    chi=chi_exact(g.adj,g.n); r=rng.random()
    low=[v for v in range(g.n) if g.degree(v)<dtarget]
    ce=[(a,b) for (a,b) in g.edges if g.chi_minus_edge(a,b)<4] if chi==4 else []
    if r<0.4 and low and ce:
        v=rng.choice(low); e=rng.choice(ce)
        col=three_coloring_of(g, exclude_edge=e)
        if col is not None:
            same=[x for x in range(g.n) if x!=v and col[x]==col[v] and not g.has(v,x)]
            if same: x=rng.choice(same); g.add(v,x); return ("add",(min(v,x),max(v,x)))
    if r<0.62:
        hi=[(a,b) for (a,b) in g.edges if g.degree(a)>dtarget+2 or g.degree(b)>dtarget+2]
        if hi: e=rng.choice(hi); g.remove(*e); return ("del",e)
    edges=tuple(g.edges)
    if len(edges)>=2:
        for _ in range(12):
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

def seed(n, dtarget, rng):
    d=max(dtarget, 3);
    if (d*n)%2: d+=1
    try: G=nx.random_regular_graph(d,n,seed=rng.randint(0,10**7))
    except Exception: G=nx.gnp_random_graph(n,0.45,seed=rng.randint(0,10**7))
    return Graph(n, list(G.edges()))

def anneal(g0, rng, lam, dtarget, iters=5000):
    g=g0.copy(); cur=score(g,lam,dtarget); bestg=g.copy(); bestsc=cur
    visited=[]  # record all (ncV,critE,minD) states seen with score accepted
    T=6.0; decay=(0.05/6.0)**(1/iters)
    for it in range(iters):
        mv=move(g,rng,dtarget)
        if mv[0]=="noop": T*=decay; continue
        new=score(g,lam,dtarget); d=new-cur
        if d<=0 or rng.random()<math.exp(-d/max(T,1e-9)):
            cur=new
            st=state(g)
            if st and st[2]>=dtarget:  # only record feasible-degree states
                visited.append(st[:2])  # (ncV, critE)
            if new<bestsc: bestsc=new; bestg=g.copy()
        else: undo(g,mv)
        T*=decay
    return visited

def pareto(points):
    """Lower-left Pareto frontier of (ncV, critE) points (minimize both)."""
    pts=sorted(set(points))
    front=[]
    best_ce=10**9
    for nc,ce in pts:  # sorted by ncV asc
        if ce<best_ce:
            front.append((nc,ce)); best_ce=ce
    return front

def main():
    rng=random.Random(271828)
    print("=== (ncV, critE) Pareto frontier per δ-target (count + wall) ===")
    print("decisive: does any frontier touch (0,0)? wall predicts convex, origin-avoiding.\n")
    for n in (13, 14):
        print(f"### n={n} ###")
        for dtarget in (4, 5, 6):
            allpts=[]
            for lam in (0.5, 1, 2, 4, 8, 16, 32):
                g=seed(n, dtarget, rng)
                pts=anneal(g, rng, lam, dtarget, iters=4000)
                allpts += pts
            front=pareto(allpts)
            hits00 = (0,0) in allpts
            # closest approach to origin (min ncV+critE among feasible)
            closest = min((nc+ce, nc, ce) for nc,ce in allpts) if allpts else (None,)
            print(f"  δ≥{dtarget}: Pareto frontier (ncV,critE) = {front}")
            print(f"     closest approach to (0,0): ncV+critE={closest[0]} at "
                  f"(ncV={closest[1]}, critE={closest[2]}); touches (0,0)? {hits00}")
            if hits00:
                print(f"     *** (0,0) REACHED at δ≥{dtarget} n={n} — WITNESS REGIME, triple-verify ***")
        print()
    print("VERDICT: per wall's prediction — is the closest approach to (0,0) at δ=5,")
    print("and is the frontier origin-avoiding (convex) at all δ-targets?")

if __name__=="__main__":
    main()
