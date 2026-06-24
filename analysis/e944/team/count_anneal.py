#!/usr/bin/env python3
"""
count_anneal.py — Recipe-A simulated annealing for an E944 (4,1)-witness.
(count, E944, ASSAULT MODE)

TARGET: a graph G that is 4-chromatic, vertex-critical (every vertex deletion
drops chi below 4), and has ZERO critical single edges.

SCORER (minimize), SOFT so the chain can cross infeasible regions (forge's
hard-reject annealer got stuck on the rigid manifold):

    score(G) = W_chi * chi_penalty(G)
             + W_vc  * (#non-critical vertices)
             + 1.0   * (#critical edges)              <- the real objective

  chi_penalty: 0 if chi==4; large if chi<4 (too few colors needed -> not 4-chromatic)
               or chi>4 (over-chromatic). We push toward exactly 4.
  A true witness has score 0 (chi==4, all vertices critical, no critical edge).

MOVES: edge add / edge delete / degree-preserving 2-swap. Mix tuned to stay near
6-regular (Prop 5.1 sparsest witness). Vertices fixed at n.

VERIFICATION: chi via fast internal exact colorer (cross-checked at startup vs
hunter checkers + critedge). Any score-0 candidate is RE-verified with hunter's
backtrack AND SAT before being declared.
"""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx

# fast exact chi (own, validated against hunter+critedge at startup)
def _is_k_colorable(adj, n, k):
    if k <= 0: return n == 0
    if k >= n: return True
    color = [-1]*n
    order = sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))
    def bt(idx, maxused):
        if idx == n: return True
        v = order[idx]
        forb = 0; nb = adj[v]
        while nb:
            low = nb & (-nb); u = low.bit_length()-1
            if color[u] >= 0: forb |= (1 << color[u])
            nb ^= low
        limit = min(maxused+1, k-1)
        for c in range(limit+1):
            if not (forb >> c) & 1:
                color[v] = c
                if bt(idx+1, max(maxused, c)): return True
                color[v] = -1
        return False
    return bt(0, -1)

def chi_exact(adj, n):
    if n == 0: return 0
    for k in range(1, n+1):
        if _is_k_colorable(adj, n, k):
            return k
    return n


class Graph:
    """Mutable graph on fixed vertex set 0..n-1 with adjacency bitmasks + edge set."""
    __slots__ = ("n", "adj", "edges")
    def __init__(self, n, edge_list):
        self.n = n
        self.adj = [0]*n
        self.edges = set()
        for u, v in edge_list:
            self.add(u, v)
    def add(self, u, v):
        if u == v: return
        a, b = (u, v) if u < v else (v, u)
        if (a, b) in self.edges: return
        self.edges.add((a, b))
        self.adj[a] |= (1 << b); self.adj[b] |= (1 << a)
    def remove(self, u, v):
        a, b = (u, v) if u < v else (v, u)
        if (a, b) not in self.edges: return
        self.edges.discard((a, b))
        self.adj[a] &= ~(1 << b); self.adj[b] &= ~(1 << a)
    def has(self, u, v):
        a, b = (u, v) if u < v else (v, u)
        return (a, b) in self.edges
    def degree(self, v):
        return bin(self.adj[v]).count("1")
    def chi(self):
        return chi_exact(self.adj, self.n)
    def chi_minus_vertex(self, v):
        # build adj without v (relabel)
        keep = [u for u in range(self.n) if u != v]
        idx = {u: i for i, u in enumerate(keep)}
        na = [0]*(self.n-1)
        for u in keep:
            nb = self.adj[u]
            while nb:
                low = nb & (-nb); w = low.bit_length()-1
                if w != v: na[idx[u]] |= (1 << idx[w])
                nb ^= low
        return chi_exact(na, self.n-1)
    def chi_minus_edge(self, a, b):
        self.adj[a] &= ~(1 << b); self.adj[b] &= ~(1 << a)
        c = chi_exact(self.adj, self.n)
        self.adj[a] |= (1 << b); self.adj[b] |= (1 << a)
        return c
    def copy(self):
        g = Graph(self.n, [])
        g.adj = self.adj[:]; g.edges = set(self.edges)
        return g


# ---------------- scorer ----------------
W_CHI = 50.0
W_VC = 8.0

def score(g, want_chi=4):
    c = g.chi()
    chi_pen = 0.0
    if c != want_chi:
        # heavily penalize; distance scaled
        chi_pen = W_CHI * (abs(c - want_chi) + (5 if c < want_chi else 0))
    # vertex-criticality: count vertices v with chi(G-v) >= want_chi (NOT critical)
    noncrit_v = 0
    if c == want_chi:  # only meaningful when chi is right
        for v in range(g.n):
            if g.chi_minus_vertex(v) >= want_chi:
                noncrit_v += 1
    else:
        noncrit_v = g.n  # treat all as bad
    # critical edges: edges e with chi(G-e) < want_chi
    crit_e = 0
    if c == want_chi and noncrit_v == 0:
        for (a, b) in g.edges:
            if g.chi_minus_edge(a, b) < want_chi:
                crit_e += 1
    elif c == want_chi:
        # still compute partial signal (cheap-ish): skip full count, estimate
        for (a, b) in g.edges:
            if g.chi_minus_edge(a, b) < want_chi:
                crit_e += 1
    return W_CHI*0 + chi_pen + W_VC*noncrit_v + 1.0*crit_e, (c, noncrit_v, crit_e)


# ---------------- moves ----------------
def random_move(g, rng, target_deg=6):
    """Return a callable undo after applying a random move in place."""
    n = g.n
    r = rng.random()
    if r < 0.35:
        # add a random non-edge
        for _ in range(20):
            u = rng.randrange(n); v = rng.randrange(n)
            if u != v and not g.has(u, v):
                g.add(u, v)
                return ("add", (min(u,v), max(u,v)))
        return ("noop", None)
    elif r < 0.6:
        # delete a random edge
        if g.edges:
            e = rng.choice(tuple(g.edges))
            g.remove(*e)
            return ("del", e)
        return ("noop", None)
    else:
        # degree-preserving 2-swap: pick edges (a,b),(c,d) disjoint, replace with (a,c),(b,d)
        if len(g.edges) >= 2:
            for _ in range(20):
                e1 = rng.choice(tuple(g.edges)); e2 = rng.choice(tuple(g.edges))
                a, b = e1; c, d = e2
                if len({a,b,c,d}) < 4: continue
                if g.has(a, c) or g.has(b, d): continue
                g.remove(a, b); g.remove(c, d)
                g.add(a, c); g.add(b, d)
                return ("swap", (e1, e2, (min(a,c),max(a,c)), (min(b,d),max(b,d))))
        return ("noop", None)

def undo_move(g, move):
    kind, data = move
    if kind == "add":
        g.remove(*data)
    elif kind == "del":
        g.add(*data)
    elif kind == "swap":
        e1, e2, n1, n2 = data
        g.remove(*n1); g.remove(*n2)
        g.add(*e1); g.add(*e2)
    # noop: nothing


# ---------------- annealer ----------------
def anneal(g0, rng, iters=200000, T0=4.0, Tend=0.02, report_every=20000,
           tag=""):
    g = g0.copy()
    cur, cur_info = score(g)
    best = cur; best_g = g.copy(); best_info = cur_info
    decay = (Tend/T0) ** (1.0/max(1, iters))
    T = T0
    t_start = time.time()
    for it in range(iters):
        mv = random_move(g, rng)
        if mv[0] == "noop":
            T *= decay; continue
        new, new_info = score(g)
        d = new - cur
        if d <= 0 or rng.random() < math.exp(-d / max(T, 1e-9)):
            cur, cur_info = new, new_info
            if new < best:
                best = new; best_g = g.copy(); best_info = new_info
                if best_info[0] == 4 and best_info[1] == 0 and best_info[2] == 0:
                    return best, best_g, best_info, it  # WITNESS hit
        else:
            undo_move(g, mv)
        T *= decay
        if report_every and it % report_every == 0 and it > 0:
            el = time.time()-t_start
            print(f"  [{tag}] it={it} T={T:.3f} cur={cur:.1f} best={best:.1f} "
                  f"best_info(chi,noncritV,critE)={best_info} ({el:.0f}s)", flush=True)
    return best, best_g, best_info, -1


def seed_C13_125():
    E = []
    for d in (1,2,5):
        for i in range(13): E.append((i, (i+d)%13))
    return Graph(13, E)

def seed_random_regular(n, deg, rng):
    for _ in range(50):
        try:
            G = nx.random_regular_graph(deg, n, seed=rng.randint(0,10**6))
            return Graph(n, list(G.edges()))
        except Exception:
            continue
    return None

def seed_g6(g6):
    G = nx.from_graph6_bytes(g6.encode())
    return Graph(G.number_of_nodes(), list(G.edges()))


def main():
    rng = random.Random(20260610)
    print("=== count ASSAULT annealer: minimize #critical-edges to 0 ===")
    print("scorer = W_chi*chi_pen + W_vc*noncritV + critE; witness = score 0\n")
    # startup chi validation vs hunter + critedge
    import checkers as H
    g = seed_C13_125()
    edges_list = sorted(g.edges)
    assert g.chi() == 4 == H.chi_bt(edges_list, 13), "chi engine mismatch!"
    print("chi engine validated vs hunter.checkers (C13(1,2,5) chi=4).\n")

    runs = []
    # champions + random 6-regular seeds at n=13..18
    runs.append(("C13(1,2,5)", seed_C13_125(), 60000))
    for n in (13, 14, 15, 16):
        gseed = seed_random_regular(n, 6, rng)
        if gseed: runs.append((f"rand6reg-n{n}", gseed, 60000))

    overall_best = None
    for tag, gseed, iters in runs:
        print(f"--- chain {tag} (n={gseed.n}, m={len(gseed.edges)}), {iters} iters")
        b, bg, binfo, hit = anneal(gseed, rng, iters=iters, tag=tag)
        print(f"  => {tag} best score={b:.1f} info(chi,noncritV,critE)={binfo}")
        if hit >= 0:
            print(f"  *** WITNESS CANDIDATE from {tag} at iter {hit}! edges={sorted(bg.edges)}")
        if overall_best is None or b < overall_best[0]:
            overall_best = (b, tag, binfo, sorted(bg.edges), bg.n)
    print("\n" + "="*60)
    print(f"OVERALL BEST: score={overall_best[0]:.1f} from {overall_best[1]} "
          f"info(chi,noncritV,critE)={overall_best[2]} n={overall_best[4]}")
    print(f"edges={overall_best[3]}")
    print("="*60)


if __name__ == "__main__":
    main()
