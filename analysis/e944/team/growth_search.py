"""
e944 A1 — criticality-preserving GROWTH search (hunter invention round 1, built for round 2).

Idea: stay ON the 4-vertex-critical manifold while growing n, instead of testing criticality after
random moves (annealing wastes ~all time off-manifold). Reach the isolated witness via a PATH of
4-vertex-critical graphs, pushing the critical-edge count down as n grows (more room).

The naive "add a pendant-ish vertex" FAILS: G+w-w = G is 4-chromatic, so w is non-critical. The
operations that genuinely preserve 4-vertex-criticality while changing the graph:
  (M1) VERTEX SPLIT: replace vertex v (deg d) by two vertices v1,v2; make v1~v2; partition N(v) plus
       possibly share some. Tune so each Gi-vi stays 3-colorable. Increases n by 1.
  (M2) HAJOS SUM of two 4-vtx-critical graphs (identify a vertex, delete two edges, add one).
  (M3) EDGE SUBDIVISION-with-triangle (Gallai): subdivide edge uv and join the new vertex to form a
       triangle-ish gadget that keeps criticality.
We do NOT derive which preserves criticality in closed form — we APPLY a candidate move and TEST the
result with checkers (4-chromatic + vertex-critical), keeping only moves that stay on-manifold, and
greedily minimizing #critical edges. This is "growth with criticality as a tested invariant."

Seed: C13(1,2,5) (the n=13 extremal, 13 critical edges). Goal: grow to n=14..20 staying
4-vertex-critical while #critical-edges drops toward 0.
"""
import sys, time, random, json, argparse
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from checkers import edges_to_adj, is_erdos944_k_r1, chi_bt
from witness_anneal import k_colorable_bt, degs


def circulant(n, conn):
    adj=[0]*n
    for v in range(n):
        for d in conn:
            for w in ((v+d)%n,(v-d)%n):
                adj[v]|=(1<<w)
    return adj


def is_4_vtx_critical(adj, n):
    if k_colorable_bt(adj,n,3): return False
    if not k_colorable_bt(adj,n,4): return False
    for v in range(n):
        keep=[u for u in range(n) if u!=v]; remap={u:i for i,u in enumerate(keep)}
        sub=[0]*(n-1)
        for u in keep:
            nb=adj[u]&~(1<<v); ru=remap[u]
            while nb:
                low=nb&(-nb); w=low.bit_length()-1; sub[ru]|=(1<<remap[w]); nb^=low
        if not k_colorable_bt(sub,n-1,3): return False
    return True


def n_critical_edges(adj, n):
    c=0
    for a in range(n):
        nb=adj[a]
        while nb:
            low=nb&(-nb); b=low.bit_length()-1; nb^=low
            if a<b:
                adj[a]&=~(1<<b); adj[b]&=~(1<<a)
                three=k_colorable_bt(adj,n,3)
                adj[a]|=(1<<b); adj[b]|=(1<<a)
                if three: c+=1
    return c


def vertex_split(adj, n, v, side_mask, rng):
    """Replace v by v1=v and v2=new index n. v1 keeps neighbors in side_mask, v2 takes the rest,
    v1~v2, and a few neighbors shared (in both) to keep degrees up. Returns (new_adj, n+1)."""
    Nv = adj[v]
    nbrs = [u for u in range(n) if (Nv>>u)&1]
    new = [adj[u] & ~(1<<v) for u in range(n)] + [0]  # drop v's old edges to its neighbors; add slot n
    v2 = n
    # clear v's row, rebuild
    new[v] = 0
    for u in nbrs:
        if (side_mask>>u)&1:
            new[v]|=(1<<u); new[u]|=(1<<v)
        else:
            new[v2]|=(1<<u); new[u]|=(1<<v2)
    # share a couple neighbors to both (keeps degrees >=6)
    share = [u for u in nbrs if rng.random()<0.5]
    for u in share:
        new[v]|=(1<<u); new[u]|=(1<<v); new[v2]|=(1<<u); new[u]|=(1<<v2)
    new[v]|=(1<<v2); new[v2]|=(1<<v)   # v1~v2
    return new, n+1


def grow(seed_adj, seed_n, budget_s, seed=0):
    rng=random.Random(seed); t0=time.time()
    adj, n = [r for r in seed_adj], seed_n
    assert is_4_vtx_critical(adj,n), "seed not 4-vtx-critical"
    best_frac=(n_critical_edges(adj,n), n)
    path=[(n, best_frac[0])]
    while time.time()-t0<budget_s and n<22:
        # try vertex-split on each vertex with random side partitions; keep a child that is
        # 4-vtx-critical with delta>=6 and the FEWEST critical edges.
        best_child=None; best_child_ce=10**9
        verts=list(range(n)); rng.shuffle(verts)
        for v in verts[:n]:
            for _try in range(6):
                Nv=[u for u in range(n) if (adj[v]>>u)&1]
                if len(Nv)<2: continue
                side=0
                for u in Nv:
                    if rng.random()<0.5: side|=(1<<u)
                child, cn = vertex_split(adj, n, v, side, rng)
                if min(degs(child,cn))<6: continue
                if not is_4_vtx_critical(child, cn): continue
                ce=n_critical_edges(child,cn)
                if ce<best_child_ce:
                    best_child_ce=ce; best_child=(child,cn)
                if ce==0:
                    edges=[(a,b) for a in range(cn) for b in range(a+1,cn) if (child[a]>>b)&1]
                    return {"witness":True,"n":cn,"edges":edges,"path":path+[(cn,0)]}
            if time.time()-t0>=budget_s: break
        if best_child is None:
            # no on-manifold split found; perturb (random restart from seed)
            adj, n = [r for r in seed_adj], seed_n
            continue
        adj, n = best_child
        path.append((n, best_child_ce))
        if (best_child_ce, n) < (best_frac[0], best_frac[1]) or best_child_ce<best_frac[0]:
            best_frac=(best_child_ce, n)
    return {"witness":False,"best_critical_edges":best_frac[0],"at_n":best_frac[1],
            "path":path,"elapsed":time.time()-t0}


if __name__=="__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("--time",type=float,default=300)
    ap.add_argument("--seed",type=int,default=0); a=ap.parse_args()
    # C13(1,2,5)
    adj=circulant(13,[1,2,5]); n=13
    print(f"# A1 GROWTH from C13(1,2,5): 4-vtx-critical={is_4_vtx_critical(adj,n)} "
          f"critical_edges={n_critical_edges(adj,n)} budget={a.time}s", flush=True)
    r=grow(adj,n,a.time,a.seed)
    if r["witness"]:
        print(f"# CANDIDATE WITNESS at n={r['n']} path={r['path']}")
        ok=is_erdos944_k_r1(r["edges"],r["n"],4,chi_fn=chi_bt)
        print(f"# checkers.py dual = {ok}")
        if ok:
            import networkx as nx
            G=nx.Graph(); G.add_nodes_from(range(r["n"])); G.add_edges_from(r["edges"])
            g6=nx.to_graph6_bytes(G,header=False).decode().strip()
            json.dump({"n":r["n"],"edges":r["edges"],"g6":g6},
                      open(f"/Users/patrickkavanagh/math/analysis/e944/team/CANDIDATE_grow_n{r['n']}.json","w"))
            print(f"# g6={g6} saved — ROUTE THROUGH skeptic_adjudicate.py")
    else:
        print(f"# no witness. best #critical-edges={r['best_critical_edges']} at n={r['at_n']}. "
              f"path(n,#crit)={r['path'][:12]} elapsed={r['elapsed']:.0f}s", flush=True)
