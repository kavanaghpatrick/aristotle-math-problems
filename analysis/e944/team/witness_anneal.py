"""
e944 EXISTENCE — targeted simulated-annealing witness search (hunter).

Rationale: complete enumeration (geng) is infeasible at n>=12 for delta>=6 (billions of graphs), and
SAT-CEGAR cannot converge on non-3-colorability discovery. So for the EXISTENCE goal we use a guided
stochastic search that tests the FULL predicate with the fast exact checker — landing even ONE
verified witness resolves the problem.

Differentiator from forge/count's stuck annealing: they searched general/sparse graphs reducing
critical-edge count. The witness lives in the DENSE regime (delta>=6, |V|>=11) that sparse-graph
moves can't reach. We search DIRECTLY in the delta>=6 / Delta<=n-5 regime, starting from random
graphs there, and use moves that preserve the degree window.

State: a graph G with all degrees in [6, n-5].
Energy (minimize): we only score graphs that are 4-vertex-critical; energy = #critical edges.
  - If G is not 4-chromatic or not vertex-critical, energy = large penalty + structural distance.
A witness = energy 0 (4-vertex-critical with zero critical edges). Verified on both checkers.

Moves: pick a present edge (a,b) and a non-edge (c,d); if swapping keeps all degrees in window, swap.
(Degree-preserving 2-swaps keep us in the regime; occasionally do add/remove respecting the window.)
"""
import sys, time, random, json, argparse
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from checkers import (edges_to_adj, is_k_colorable_sat, is_erdos944_k_r1, chi_bt)


def k_colorable_bt(adj, n, k):
    """Fast k-colorability, DSATUR-ordered backtracking."""
    color = [-1]*n
    order = sorted(range(n), key=lambda v:-bin(adj[v]).count("1"))
    def bt(i, mx):
        if i==n: return True
        v=order[i]; forb=0; nb=adj[v]
        while nb:
            low=nb&(-nb); u=low.bit_length()-1
            if color[u]>=0: forb|=(1<<color[u])
            nb^=low
        lim=min(mx+1,k-1)
        for c in range(lim+1):
            if not (forb>>c)&1:
                color[v]=c
                if bt(i+1,max(mx,c)): return True
                color[v]=-1
        return False
    return bt(0,-1)


def degs(adj, n):
    return [bin(adj[v]).count("1") for v in range(n)]


def score(adj, n):
    """Return (energy, is_witness). Lower energy = closer to witness.
    Penalty structure pushes toward 4-chromatic + vertex-critical first, then 0 critical edges."""
    # chi>=4 ? (not 3-colorable)
    if k_colorable_bt(adj, n, 3):
        # 3-colorable: far away. energy huge; tie-break by (4 - would-be-chi) proxy = #edges deficit
        return 100000 - sum(degs(adj,n)), False
    # chi<=4 ?
    if not k_colorable_bt(adj, n, 4):
        return 90000, False  # chi>=5, too dense in the wrong way
    # chi==4. vertex-critical? count non-critical vertices (want all critical)
    noncrit = 0
    for v in range(n):
        # G-v 3-colorable?
        sub_adj=[0]*(n-1); keep=[u for u in range(n) if u!=v]; remap={u:i for i,u in enumerate(keep)}
        for u in keep:
            nb=adj[u]&~(1<<v); ru=remap[u]
            while nb:
                low=nb&(-nb); w=low.bit_length()-1; sub_adj[ru]|=(1<<remap[w]); nb^=low
        if not k_colorable_bt(sub_adj, n-1, 3):
            noncrit += 1  # v is NOT critical (G-v still 4-chromatic)
    if noncrit > 0:
        return 1000 + noncrit, False  # 4-chromatic but not vertex-critical
    # 4-vertex-critical! count critical edges (want 0)
    crit = 0
    for a in range(n):
        nb=adj[a]
        while nb:
            low=nb&(-nb); b=low.bit_length()-1; nb^=low
            if a<b:
                adj[a]&=~(1<<b); adj[b]&=~(1<<a)
                three=k_colorable_bt(adj,n,3)
                adj[a]|=(1<<b); adj[b]|=(1<<a)
                if three: crit+=1
    return crit, (crit==0)


def random_regular_ish(n, target_deg, rng):
    """Random graph with all degrees ~target_deg (configuration-model style, then repaired)."""
    import networkx as nx
    for _ in range(200):
        try:
            G = nx.random_regular_graph(target_deg, n, seed=rng.randint(0, 1<<30))
            if nx.is_connected(G):
                adj=[0]*n
                for (u,v) in G.edges(): adj[u]|=(1<<v); adj[v]|=(1<<u)
                return adj
        except Exception:
            continue
    return None


def _edge_list(adj, n):
    edges=[]
    for a in range(n):
        nb=adj[a]
        while nb:
            low=nb&(-nb); b=low.bit_length()-1; nb^=low
            if a<b: edges.append((a,b))
    return edges


def neighbors_swap(adj, n, rng, lo, hi):
    """Mixed move set within the degree window [lo,hi]:
      - 70%: degree-preserving double-edge swap (a,b),(c,d) -> (a,d),(c,b)
      - 15%: add an edge (both endpoints have degree < hi)
      - 15%: remove an edge (both endpoints have degree > lo)
    Exploring the full window (not just 6-regular) opens the space the witness may live in."""
    edges=_edge_list(adj, n)
    if len(edges)<2: return None
    r=rng.random()
    ds=degs(adj,n)
    if r < 0.70:
        for _ in range(40):
            (a,b),(c,d)=rng.sample(edges,2)
            if len({a,b,c,d})<4: continue
            if (adj[a]>>d)&1 or (adj[c]>>b)&1: continue
            na=[row for row in adj]
            na[a]&=~(1<<b); na[b]&=~(1<<a); na[c]&=~(1<<d); na[d]&=~(1<<c)
            na[a]|=(1<<d); na[d]|=(1<<a); na[c]|=(1<<b); na[b]|=(1<<c)
            nds=degs(na,n)
            if all(lo<=x<=hi for x in nds): return na
        return None
    elif r < 0.85:
        # add edge
        cand=[v for v in range(n) if ds[v]<hi]
        for _ in range(40):
            if len(cand)<2: break
            a,b=rng.sample(cand,2)
            if a>b: a,b=b,a
            if (adj[a]>>b)&1: continue
            na=[row for row in adj]; na[a]|=(1<<b); na[b]|=(1<<a)
            return na
        return None
    else:
        # remove edge
        cand_e=[(a,b) for (a,b) in edges if ds[a]>lo and ds[b]>lo]
        if not cand_e: return None
        a,b=rng.choice(cand_e)
        na=[row for row in adj]; na[a]&=~(1<<b); na[b]&=~(1<<a)
        return na


def random_irregular_seed(n, rng, lo=6, hi=None):
    """Random connected graph with degrees in [lo,hi], NOT necessarily regular. Start near 6-regular
    then add a few random edges to break regularity (explores the irregular delta>=6 regime that
    skeptic's EXHAUSTIVE 6-regular sweep does not cover)."""
    hi = hi if hi else n-5
    adj = random_regular_ish(n, lo, rng)
    if adj is None: return None
    ds = degs(adj, n)
    extra = rng.randint(0, max(0, (hi-lo))) * (n//3)  # a handful of extra edges
    for _ in range(extra):
        cand=[v for v in range(n) if ds[v]<hi]
        if len(cand)<2: break
        a,b=rng.sample(cand,2)
        if a>b: a,b=b,a
        if (adj[a]>>b)&1: continue
        adj[a]|=(1<<b); adj[b]|=(1<<a); ds[a]+=1; ds[b]+=1
    return adj


def anneal(n, seed, budget_s, lo=6, hi=None, restarts=10000, irregular=True):
    hi = hi if hi else n-5
    rng = random.Random(seed)
    t0=time.time(); best=10**9; best_adj=None; tries=0
    while time.time()-t0 < budget_s:
        tries+=1
        adj = (random_irregular_seed(n, rng, lo, hi) if irregular
               else random_regular_ish(n, lo, rng))
        if adj is None: continue
        cur,_ = score(adj, n)
        T=3.0
        steps = 800
        for s in range(steps):
            if time.time()-t0 >= budget_s: break
            nadj = neighbors_swap(adj, n, rng, lo, hi)
            if nadj is None: continue
            e,is_w = score(nadj, n)
            if is_w:
                return {"witness": True, "n": n, "adj": nadj, "tries": tries, "elapsed": time.time()-t0}
            if e <= cur or rng.random() < pow(2.718, -(e-cur)/max(T,1e-6)):
                adj=nadj; cur=e
                if cur<best:
                    best=cur; best_adj=[r for r in adj]
            T*=0.995
    return {"witness": False, "n": n, "best_energy": best, "best_adj": best_adj,
            "tries": tries, "elapsed": time.time()-t0}


def adj_to_edges(adj, n):
    out=[]
    for a in range(n):
        nb=adj[a]
        while nb:
            low=nb&(-nb); b=low.bit_length()-1; nb^=low
            if a<b: out.append((a,b))
    return out


if __name__ == "__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("--time", type=float, default=600)
    ap.add_argument("--seed", type=int, default=0)
    args=ap.parse_args()
    print(f"# anneal witness search n={args.n} budget={args.time}s seed={args.seed}", flush=True)
    r=anneal(args.n, args.seed, args.time)
    if r["witness"]:
        edges=adj_to_edges(r["adj"], args.n)
        ok_bt = is_erdos944_k_r1(edges, args.n, 4, chi_fn=chi_bt)
        print(f"# CANDIDATE WITNESS n={args.n} tries={r['tries']} — verifying (checkers.py)...")
        print(f"# checkers.py backtrack IsErdos944(4,1) = {ok_bt}")
        # build graph6 for skeptic's THIRD independent adjudicator (chi_A + chi_B must agree)
        import networkx as nx, subprocess
        G=nx.Graph(); G.add_nodes_from(range(args.n)); G.add_edges_from(edges)
        g6=nx.to_graph6_bytes(G, header=False).decode().strip()
        with open(f"/Users/patrickkavanagh/math/analysis/e944/team/CANDIDATE_n{args.n}.json","w") as f:
            json.dump({"n":args.n,"edges":edges,"g6":g6}, f)
        print(f"# g6={g6}  (saved CANDIDATE_n{args.n}.json)")
        # PROTOCOL (skeptic): route through skeptic_adjudicate.py BEFORE declaring witness.
        try:
            out=subprocess.run(["python3","/Users/patrickkavanagh/math/analysis/e944/team/skeptic_adjudicate.py",
                                 "--g6",g6], capture_output=True, text=True, timeout=300).stdout
            print("# ADJUDICATOR:", out.strip())
            adj_ok = "WITNESS" in out.upper() and "NOT A WITNESS" not in out.upper()
        except Exception as ex:
            print(f"# adjudicator error: {ex}"); adj_ok=False
        if ok_bt and adj_ok:
            with open(f"/Users/patrickkavanagh/math/analysis/e944/team/WITNESS_n{args.n}.json","w") as f:
                json.dump({"n":args.n,"edges":edges,"g6":g6}, f)
            print(f"# !!!!!!! TRIPLE-CONFIRMED WITNESS (anneal model + checkers.py + skeptic chi_A/chi_B) "
                  f"— saved WITNESS_n{args.n}.json !!!!!!!")
            print(f"# edges={edges}")
        else:
            print(f"# candidate did NOT pass triple-check (checkers={ok_bt} adjudicator={adj_ok}) — NOT a witness.")
    else:
        print(f"# no witness. best_energy(min #critical-edges among 4-vtx-critical)={r['best_energy']} "
              f"tries={r['tries']} elapsed={r['elapsed']:.0f}s", flush=True)
