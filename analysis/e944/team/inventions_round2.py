#!/usr/bin/env python3
"""
inventions_round2.py — count-lane inventions CNT-4/5/6 (E944 invention blitz R2).
Builds on R1 lessons: CNT-1 drift along trade curve -> corner-seeking PRODUCT
potential (CNT-4); CNT-2 add-inflated coupling -> fair swap-based coupling (CNT-5);
new construction object: twin-vertex graft (CNT-6).
"""
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
from count_anneal3 import three_coloring_of
import networkx as nx


def circ(n, S):
    E = []
    for d in S:
        for i in range(n): E.append((i, (i+d) % n))
    return Graph(n, E)


def feasinfo(g):
    chi = chi_exact(g.adj, g.n)
    if chi != 4:
        return (chi, g.n, g.number_of_edges_critical() if False else 0, 0)
    ncv = sum(1 for v in range(g.n) if g.chi_minus_vertex(v) >= 4)
    ce = sum(1 for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4)
    mind = min(g.degree(v) for v in range(g.n))
    return (chi, ncv, ce, mind)


# 2-swap helpers
def two_swap(g, rng):
    edges = tuple(g.edges)
    if len(edges) < 2: return ("noop", None)
    for _ in range(20):
        a,b = rng.choice(edges); c,d = rng.choice(edges)
        if len({a,b,c,d})<4: continue
        for e1,e2 in [((a,c),(b,d)),((a,d),(b,c))]:
            if not g.has(*e1) and not g.has(*e2):
                g.remove(a,b); g.remove(c,d); g.add(*e1); g.add(*e2)
                return ("swap",((min(a,b),max(a,b)),(min(c,d),max(c,d)),
                                (min(*e1),max(*e1)),(min(*e2),max(*e2))))
    return ("noop", None)

def undo_swap(g, mv):
    if mv[0]!="swap": return
    o1,o2,n1,n2 = mv[1]; g.remove(*n1); g.remove(*n2); g.add(*o1); g.add(*o2)


# ============================================================
# CNT-4 — corner-seeking PRODUCT potential
# ============================================================
def product_potential(g):
    chi = chi_exact(g.adj, g.n)
    if chi != 4:
        return 1000 + 50*(abs(chi-4)+(5 if chi<4 else 0)), (chi,)
    ncv = sum(1 for v in range(g.n) if g.chi_minus_vertex(v) >= 4)
    ce = sum(1 for (a,b) in g.edges if g.chi_minus_edge(a,b) < 4)
    mind = min(g.degree(v) for v in range(g.n))
    pen = 0 if mind>=6 else 20*(6-mind)
    # corner-seeking: product is 0 only when one of them is 0; +sum to then descend axis
    return ce*ncv*1.0 + (ce+ncv) + pen, (chi, ncv, ce, mind)

def run_cnt4(iters=10000):
    print("### CNT-4 corner-seeking product potential ###")
    rng = random.Random(11)
    best=None
    for name,g0 in [("C13(1,2,5)",circ(13,[1,2,5])),("C16(1,2,5)",circ(16,[1,2,5])),
                    ("C14(1,2,5)",circ(14,[1,2,5]))]:
        g=g0.copy(); cur,info=product_potential(g); b=cur; bi=info
        T=4.0; decay=(0.02/4.0)**(1/iters)
        for it in range(iters):
            mv=two_swap(g,rng)
            if mv[0]=="noop": T*=decay; continue
            new,ninfo=product_potential(g); d=new-cur
            if d<=0 or rng.random()<math.exp(-d/max(T,1e-9)):
                cur,info=new,ninfo
                if new<b: b=new; bi=ninfo
                if len(bi)==4 and bi[1]==0 and bi[2]==0 and bi[3]>=6:
                    print(f"  *** WITNESS from {name}! ***"); return ("WITNESS",name,g.copy())
            else: undo_swap(g,mv)
            T*=decay
        print(f"  from {name}: best Φ_prod={b:.0f} info(chi,ncV,critE,minD)={bi}")
        if best is None or b<best[0]: best=(b,name,bi)
    print(f"  VERDICT: best product-potential={best[0]:.0f} info={best[2]} "
          f"({'corner reached' if best[0]==0 else 'no corner — both ledgers stay positive'})")
    return best


# ============================================================
# CNT-5 — fair swap-based coupling (degree-preserving de-criticalize)
# ============================================================
def fair_decrit_damage(g, e):
    """De-criticalize edge e by a degree-preserving 2-swap that breaks a 3-coloring
    of G-e, then count vertices made non-critical. Fairer than add (no densify)."""
    u,v=e
    col=three_coloring_of(g, exclude_edge=(u,v))
    if col is None: return None
    by={0:[],1:[],2:[]}
    for w in range(g.n): by[col[w]].append(w)
    for c in (0,1,2):
        cand=by[c]
        for i in range(len(cand)):
            for j in range(i+1,len(cand)):
                x,y=cand[i],cand[j]
                if g.has(x,y): continue
                xn=[w for w in range(g.n) if g.has(x,w) and w!=y]
                yn=[w for w in range(g.n) if g.has(y,w) and w!=x]
                for p in xn:
                    for q in yn:
                        if len({x,y,p,q})<4 or g.has(p,q): continue
                        g.remove(x,p); g.remove(y,q); g.add(x,y); g.add(p,q)
                        dmg=0
                        if chi_exact(g.adj,g.n)==4:
                            dmg=sum(1 for w in range(g.n) if g.chi_minus_vertex(w)>=4)
                        g.remove(x,y); g.remove(p,q); g.add(x,p); g.add(y,q)
                        return dmg
    return None

def run_cnt5():
    print("\n### CNT-5 fair swap-based coupling ###")
    for name,g in [("C13(1,2,5)",circ(13,[1,2,5])),("C16(1,2,5)",circ(16,[1,2,5]))]:
        crit=[(a,b) for (a,b) in g.edges if g.chi_minus_edge(a,b)<4]
        dmgs=[]
        for e in crit:
            d=fair_decrit_damage(g,e)
            if d is not None: dmgs.append(d)
        if dmgs:
            print(f"  {name}: fair (swap-based) edge-fix damage avg={sum(dmgs)/len(dmgs):.2f} "
                  f"min={min(dmgs)} max={max(dmgs)} over {len(dmgs)} edges")
    print("  VERDICT: if fair damage still HIGH (>=1 avg), entanglement is real not")
    print("  an add-artifact; if LOW, R1 coupling was inflated by densification.")


# ============================================================
# CNT-6 — twin-vertex graft (coupled construction)
# ============================================================
def twin_vertex(g, v):
    """Add v' = twin of v: N(v')=N(v), no edge v-v'. Returns new Graph (n+1)."""
    new_n=g.n+1; vp=g.n
    edges=list(g.edges)
    for w in range(g.n):
        if g.has(v,w): edges.append((w,vp))
    return Graph(new_n, edges)

def run_cnt6():
    print("\n### CNT-6 twin-vertex graft ###")
    # twin a vertex of C13(1,2,5), then rewire to restore vertex-criticality, watch critE
    rng=random.Random(6)
    g0=circ(13,[1,2,5])
    results=[]
    for v in range(3):  # try twinning a few vertices
        g=twin_vertex(g0,v)
        chi=chi_exact(g.adj,g.n)
        ncv=sum(1 for w in range(g.n) if g.chi_minus_vertex(w)>=4) if chi==4 else g.n
        ce=sum(1 for (a,b) in g.edges if g.chi_minus_edge(a,b)<4) if chi==4 else -1
        mind=min(g.degree(w) for w in range(g.n))
        results.append((v,g.n,chi,ncv,ce,mind))
        print(f"  twin v={v}: n={g.n} chi={chi} ncV={ncv} critE={ce} minD={mind}")
    print("  VERDICT: twinning a vertex of a (n≡1) vertex-critical circulant —")
    print("  does the twin pair stay critical (ncV low) while critE drops? "
          "(twins are typically NON-critical → ncV jumps, expected to fail but cheap to confirm)")
    return results


if __name__ == "__main__":
    r4=run_cnt4()
    r5=run_cnt5()
    r6=run_cnt6()
    print("\n=== ROUND 2 SUMMARY ===")
    print("CNT-4 product-potential:", r4[0] if r4 and r4[0]!='WITNESS' else r4)
    print("CNT-6 twin grafts tested:", len(r6))
