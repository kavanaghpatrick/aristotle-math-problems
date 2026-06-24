"""
e944 A2 — REVERSE SEARCH (hunter invention round 1).

Every prior search held VERTEX-CRITICALITY fixed and chased no-critical-edge (and plateaued at 13).
This does the REVERSE: hold NO-CRITICAL-EDGE as the invariant, chase vertex-criticality.

Rationale (count's debt-trade): the two conditions are antagonistic. A DENSE 4-chromatic graph
trivially has NO critical edge (removing one edge leaves ample 4-chromatic structure). So start dense
(0 critical edges, invariant satisfied) and DELETE edges to drive every vertex toward critical, while
NEVER letting an edge become critical and keeping delta>=6. If a "no-critical-edge corridor" reaches a
vertex-critical graph, that graph is a WITNESS. If it plateaus with non-critical vertices remaining
while every further valid deletion would create a critical edge, the corridor is blocked (a new
impossibility datum).

State invariant maintained: chi(G)=4 AND no edge is critical AND delta>=6.
Objective minimized: number of NON-critical vertices (0 = vertex-critical = witness).
Move: delete an edge (a,b) iff after deletion (i) delta>=6 still, (ii) chi still 4, (iii) still NO
critical edge. Among valid deletions pick the one maximizing #critical vertices (greedy), with random
tie-break and restarts.
"""
import sys, time, random, json, argparse
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from checkers import edges_to_adj, is_erdos944_k_r1, chi_bt
from witness_anneal import k_colorable_bt, degs


def _adj_del(adj, a, b):
    adj[a] &= ~(1 << b); adj[b] &= ~(1 << a)
def _adj_add(adj, a, b):
    adj[a] |= (1 << b); adj[b] |= (1 << a)


def is_4chromatic(adj, n):
    return (not k_colorable_bt(adj, n, 3)) and k_colorable_bt(adj, n, 4)


def has_no_critical_edge(adj, n):
    """no edge e has chi(G-e)=3 (G known 4-chromatic). True = invariant holds."""
    for a in range(n):
        nb = adj[a]
        while nb:
            low = nb & (-nb); b = low.bit_length()-1; nb ^= low
            if a < b:
                _adj_del(adj, a, b)
                three = k_colorable_bt(adj, n, 3)
                _adj_add(adj, a, b)
                if three:
                    return False
    return True


def n_noncritical_vertices(adj, n):
    """count vertices v with chi(G-v)=4 (NOT critical). 0 = vertex-critical."""
    cnt = 0
    for v in range(n):
        keep=[u for u in range(n) if u!=v]; remap={u:i for i,u in enumerate(keep)}
        sub=[0]*(n-1)
        for u in keep:
            nb=adj[u]&~(1<<v); ru=remap[u]
            while nb:
                low=nb&(-nb); w=low.bit_length()-1; sub[ru]|=(1<<remap[w]); nb^=low
        if not k_colorable_bt(sub, n-1, 3):
            cnt += 1
    return cnt


def dense_4chromatic_seed(n, rng, target_edges):
    """Random graph with ~target_edges edges that is 4-chromatic (dense, so 0 critical edges likely)."""
    import networkx as nx
    for _ in range(100):
        p = target_edges / (n*(n-1)/2)
        G = nx.gnp_random_graph(n, p, seed=rng.randint(0,1<<30))
        if not nx.is_connected(G): continue
        adj = edges_to_adj([(u,v) for u,v in G.edges()], n)
        if min(degs(adj,n)) < 6: continue
        if is_4chromatic(adj, n):
            return adj
    return None


def reverse_search(n, seed, budget_s):
    rng = random.Random(seed)
    t0 = time.time(); best_noncrit = 10**9; best_adj=None; restarts=0
    while time.time()-t0 < budget_s:
        restarts += 1
        # seed: dense 4-chromatic, ~ n*(n-1)/3 edges (well above delta>=6 floor of 3n)
        adj = dense_4chromatic_seed(n, rng, int(n*(n-1)/2 * 0.55))
        if adj is None: continue
        if not has_no_critical_edge(adj, n):
            continue  # seed not on the invariant; try denser
        # greedy deletion preserving the invariant, minimizing non-critical vertices
        improved = True
        while improved and time.time()-t0 < budget_s:
            improved = False
            cur_nc = n_noncritical_vertices(adj, n)
            if cur_nc == 0:
                # vertex-critical AND no critical edge AND 4-chromatic = WITNESS
                edges=[(a,b) for a in range(n) for b in range(a+1,n) if (adj[a]>>b)&1]
                return {"witness": True, "n": n, "adj": adj, "edges": edges, "restarts": restarts}
            if cur_nc < best_noncrit:
                best_noncrit = cur_nc; best_adj=[r for r in adj]
            ds = degs(adj, n)
            edges=[(a,b) for a in range(n) for b in range(a+1,n) if (adj[a]>>b)&1]
            rng.shuffle(edges)
            best_move=None; best_move_nc=cur_nc
            for (a,b) in edges:
                if ds[a]<=6 or ds[b]<=6: continue   # keep delta>=6
                _adj_del(adj,a,b)
                ok = is_4chromatic(adj,n) and has_no_critical_edge(adj,n)
                if ok:
                    nc = n_noncritical_vertices(adj,n)
                    if nc < best_move_nc:
                        best_move_nc = nc; best_move=(a,b)
                _adj_add(adj,a,b)
                if best_move_nc==0: break
            if best_move is not None:
                _adj_del(adj, *best_move); ds=degs(adj,n); improved=True
    return {"witness": False, "n": n, "best_noncrit": best_noncrit, "best_adj": best_adj,
            "restarts": restarts, "elapsed": time.time()-t0}


if __name__ == "__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("n",type=int)
    ap.add_argument("--time",type=float,default=300); ap.add_argument("--seed",type=int,default=0)
    a=ap.parse_args()
    print(f"# REVERSE SEARCH n={a.n} budget={a.time}s seed={a.seed} "
          f"(invariant=no-critical-edge, objective=vertex-criticality)", flush=True)
    r=reverse_search(a.n, a.seed, a.time)
    if r["witness"]:
        ok=is_erdos944_k_r1(r["edges"], a.n, 4, chi_fn=chi_bt)
        print(f"# CANDIDATE WITNESS n={a.n} — checkers.py dual = {ok}")
        if ok:
            import networkx as nx
            G=nx.Graph(); G.add_nodes_from(range(a.n)); G.add_edges_from(r["edges"])
            g6=nx.to_graph6_bytes(G,header=False).decode().strip()
            json.dump({"n":a.n,"edges":r["edges"],"g6":g6},
                      open(f"/Users/patrickkavanagh/math/analysis/e944/team/CANDIDATE_rev_n{a.n}.json","w"))
            print(f"# g6={g6} saved CANDIDATE_rev_n{a.n}.json — ROUTE THROUGH skeptic_adjudicate.py")
    else:
        print(f"# no witness. min #non-critical vertices reached = {r['best_noncrit']} "
              f"(0 would be a witness) restarts={r['restarts']} elapsed={r['elapsed']:.0f}s", flush=True)
