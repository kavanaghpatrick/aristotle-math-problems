#!/usr/bin/env python3
"""
inventions_round1.py — cheap kill-tests for count-lane inventions CNT-1/2/3.
(count, E944 invention blitz)
Engine: count_anneal.Graph + critedge chi. All χ exact.
"""
import sys, os, random, math, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
import networkx as nx


def circ(n, S):
    E = []
    for d in S:
        for i in range(n): E.append((i, (i+d) % n))
    return Graph(n, E)


# ============================================================
# CNT-2 — entanglement-direct scorer (cheapest, run first)
# ============================================================
def cheapest_decriticalize_edit(g, e):
    """For critical edge e=uv, the cheapest local edit to de-criticalize it: add one
    edge between two same-colored vertices in a 3-coloring of G-e. Return the set of
    vertices that BECOME non-critical after that edit (damage to vertex-criticality)."""
    from count_anneal3 import three_coloring_of
    u, v = e
    col = three_coloring_of(g, exclude_edge=(u, v))
    if col is None:
        return set()
    by = {0: [], 1: [], 2: []}
    for w in range(g.n): by[col[w]].append(w)
    # add one same-colored non-adjacent pair
    for c in (0, 1, 2):
        cand = by[c]
        for i in range(len(cand)):
            for j in range(i+1, len(cand)):
                x, y = cand[i], cand[j]
                if not g.has(x, y):
                    g.add(x, y)
                    # which vertices are now non-critical?
                    damaged = set()
                    if chi_exact(g.adj, g.n) == 4:
                        for w in range(g.n):
                            if g.chi_minus_vertex(w) >= 4:
                                damaged.add(w)
                    g.remove(x, y)
                    return damaged
    return set()


def coupling_score(g):
    """Entanglement: how much fixing critical edges damages vertex-criticality."""
    chi = chi_exact(g.adj, g.n)
    if chi != 4:
        return None
    crit = [(a, b) for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4]
    total_damage = 0
    for e in crit:
        total_damage += len(cheapest_decriticalize_edit(g, e))
    return {"critE": len(crit), "edge_fix_damage": total_damage,
            "avg_damage_per_edge": total_damage/len(crit) if crit else 0}


def run_cnt2():
    print("### CNT-2 entanglement scorer ###")
    rng = random.Random(1)
    seeds = {"C13(1,2,5)": circ(13, [1,2,5]), "C16(1,2,5)": circ(16, [1,2,5])}
    import networkx as nx
    for n in (13, 14):
        for t in range(2):
            try:
                G = nx.random_regular_graph(6, n, seed=rng.randint(0,10**6))
                g = Graph(n, list(G.edges()))
                if chi_exact(g.adj, g.n) == 4 and all(g.chi_minus_vertex(v)<4 for v in range(n)):
                    seeds[f"rand6reg-n{n}-{t}"] = g
            except Exception: pass
    results = []
    for name, g in seeds.items():
        cs = coupling_score(g)
        print(f"  {name}: {cs}")
        if cs: results.append((name, cs))
    if results:
        dmgs = [r[1]["avg_damage_per_edge"] for r in results]
        print(f"  -> avg edge-fix-damage range: {min(dmgs):.2f}..{max(dmgs):.2f}")
        print("  VERDICT:", "HIGH coupling everywhere (impossibility signal)" if min(dmgs) >= 1
              else "some LOW coupling found — lead!")
    return results


# ============================================================
# CNT-1 — pair-move SA on combined potential
# ============================================================
def combined_potential(g):
    chi = chi_exact(g.adj, g.n)
    if chi != 4:
        return 50*(abs(chi-4)+ (5 if chi<4 else 0)) + 100, None
    ncv = sum(1 for v in range(g.n) if g.chi_minus_vertex(v) >= 4)
    ce = sum(1 for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4)
    mind = min(g.degree(v) for v in range(g.n))
    pen = 0 if mind >= 6 else 6*(6-mind)
    return ncv + ce + pen, (chi, ncv, ce, mind)


def pair_move(g, rng):
    """Act on a (critical edge, non-critical vertex) pair: add an edge incident to a
    non-critical vertex that ALSO breaks a critical edge's forcing coloring; remove an
    edge to preserve degree. Falls back to degree-preserving 2-swap."""
    from count_anneal3 import three_coloring_of
    chi = chi_exact(g.adj, g.n)
    crit = [(a, b) for (a, b) in g.edges if g.chi_minus_edge(a, b) < 4] if chi==4 else []
    ncv = [v for v in range(g.n) if g.chi_minus_vertex(v) >= 4] if chi==4 else []
    if crit and ncv:
        e = rng.choice(crit); w = rng.choice(ncv)
        col = three_coloring_of(g, exclude_edge=e)
        if col is not None:
            # connect w to a same-colored vertex (forces conflict at w's class) — degree-
            # preserving: also remove one of w's existing edges
            same = [x for x in range(g.n) if x != w and col[x]==col[w] and not g.has(w,x)]
            wn = [x for x in range(g.n) if g.has(w,x)]
            if same and wn:
                x = rng.choice(same); p = rng.choice(wn)
                # 2-swap: remove (w,p) and an edge at x, add (w,x) and reconnect
                xn = [y for y in range(g.n) if g.has(x,y) and y not in (w,p)]
                if xn:
                    q = rng.choice(xn)
                    if not g.has(p,q) and len({w,x,p,q})==4:
                        g.remove(w,p); g.remove(x,q); g.add(w,x); g.add(p,q)
                        return ("swap",((min(w,p),max(w,p)),(min(x,q),max(x,q)),
                                        (min(w,x),max(w,x)),(min(p,q),max(p,q))))
    # fallback degree-preserving 2-swap
    edges = tuple(g.edges)
    if len(edges) >= 2:
        for _ in range(15):
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
    o1,o2,n1,n2 = mv[1]
    g.remove(*n1); g.remove(*n2); g.add(*o1); g.add(*o2)


def run_cnt1(iters=8000):
    print("\n### CNT-1 pair-move SA ###")
    rng = random.Random(2)
    best_overall = 999
    for name, g0 in [("C13(1,2,5)", circ(13,[1,2,5])), ("C14(1,2,5)", circ(14,[1,2,5]))]:
        g = g0.copy()
        cur, info = combined_potential(g); best = cur; binfo = info
        T=3.0; decay=(0.02/3.0)**(1/iters)
        for it in range(iters):
            mv = pair_move(g, rng)
            if mv[0]=="noop": T*=decay; continue
            new, ninfo = combined_potential(g); d=new-cur
            if d<=0 or rng.random()<math.exp(-d/max(T,1e-9)):
                cur,info=new,ninfo
                if new<best: best=new; binfo=ninfo
            else: undo_swap(g,mv)
            T*=decay
        print(f"  from {name}: best Φ={best} info(chi,ncV,critE,minD)={binfo}")
        best_overall = min(best_overall, best)
    print(f"  VERDICT: best combined Φ reached = {best_overall} "
          f"({'BELOW 13 — gap crossed!' if best_overall<13 else 'NOT below 13 — pair-move stuck'})")
    return best_overall


# ============================================================
# CNT-3 — monodromy-obstructed voltage search
# ============================================================
def derived_graph(base_edges, b, voltages, m):
    """Regular Z_m cover: vertices (i,t), edge (u,t)-(v,(t+g)%m) for base edge (u,v,g)."""
    G = nx.Graph()
    for i in range(b):
        for t in range(m): G.add_node((i,t))
    for (u,v,g) in voltages:
        for t in range(m):
            G.add_edge((u,t),(v,(t+g)%m))
    nodes=list(G.nodes()); idx={x:i for i,x in enumerate(nodes)}
    gg=Graph(len(nodes), [(idx[a],idx[b2]) for a,b2 in G.edges()])
    return gg


def run_cnt3():
    print("\n### CNT-3 monodromy voltage search ###")
    # base = C5 (3-chromatic), assign Z_m voltages, see if cover lifts to chi=4
    found=[]
    bases = {"C5": ([(0,1),(1,2),(2,3),(3,4),(4,0)],5),
             "C7": ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,0)],7)}
    import itertools
    tested=0; lifted=0
    for bname,(be,b) in bases.items():
        for m in (3,4,5):
            # try all voltage assignments in {0..m-1}^|be| (cap to avoid blowup)
            allg = list(itertools.product(range(m), repeat=len(be)))
            if len(allg)>4000: allg=allg[:4000]
            for gv in allg:
                voltages=[(be[i][0],be[i][1],gv[i]) for i in range(len(be))]
                gg=derived_graph(be,b,voltages,m)
                tested+=1
                c=chi_exact(gg.adj,gg.n)
                if c==4:
                    lifted+=1
                    vc=all(gg.chi_minus_vertex(v)<4 for v in range(gg.n))
                    mind=min(gg.degree(v) for v in range(gg.n))
                    if vc and mind>=4:
                        ce=sum(1 for (a,bb) in gg.edges if gg.chi_minus_edge(a,bb)<4)
                        found.append((bname,m,gg.n,mind,ce))
    print(f"  tested {tested} covers, {lifted} lifted to chi=4")
    if found:
        found.sort(key=lambda x:x[4])
        print(f"  chi=4 vertex-critical covers: {len(found)}; best:")
        for f in found[:5]:
            print(f"    base={f[0]} m={f[1]} n={f[2]} min-deg={f[3]} critical-edges={f[4]} "
                  f"(ratio {f[4]/f[2]:.2f})")
        print("  VERDICT:", "monodromy lift WORKS, escalate best" if found[0][4]<found[0][2]/3
              else "lifts exist but floor >= n/3 — no improvement")
    else:
        print("  VERDICT: NO chi=4 vertex-critical cover — monodromy route dead (cheap kill)")
    return found


if __name__ == "__main__":
    r2 = run_cnt2()
    r1 = run_cnt1()
    r3 = run_cnt3()
    print("\n=== ROUND 1 INVENTION KILL-TEST SUMMARY ===")
    print("CNT-2 entanglement:", "computed" if r2 else "n/a")
    print("CNT-1 pair-move best Φ:", r1)
    print("CNT-3 monodromy covers found:", len(r3))
