#!/usr/bin/env python3
"""
forge_family_portrait.py — JOINT zero-free portrait of the deleted-edge polynomial
FAMILY {P(G−e, x) : e ∈ E} near x = k−1, for the impossibility proof.

team-lead reframe: gallai killed the single-polynomial lever (B₁ is NOT a function
of P(G,x) alone). The LIVE lever is the JOINT zero-free question on the FAMILY of
edge-deleted chromatic polynomials. Nobody has computed these portraits.

For each target graph G (χ=k), and for q=k−1 (=3 for k=4, =4 for k=5 control):
  - for EVERY edge e, compute P(G−e, x) and its REAL ROOT(S) nearest q, plus the
    VALUE P(G−e, q) (= B₁ contribution; >0 iff e is critical) and the local sign /
    derivative at q.
  - PORTRAIT: how the |E| polynomials' near-q roots cluster; do they straddle q
    (some root just below, some just above)? does |E*|=0 (all P(G−e,q)=0, i.e. q is
    a root of EVERY family member) force a COMMON structure (e.g. all family members
    have a root AT q, i.e. q is a shared root of the whole family)?
  - DISTINGUISH vertex-critical hosts (the target object) vs non-vertex-critical
    hosts (the |E*|=0 near-misses like cocktail/K(6,2)).

KEY OBSERVATION to test: e critical ⟺ P(G−e, q) > 0 (G−e is q-colorable). |E*|=0 ⟺
P(G−e, q) = 0 for EVERY e ⟺ q is a root of EVERY member of the family {P(G−e,x)}.
So |E*|=0 ⟺ x=q is a COMMON root of the whole edge-deleted family. The joint
zero-free lever: can x=q be a common root of all P(G−e,x) while G is q+1 chromatic
AND vertex-critical? The portrait shows the root MULTIPLICITY / clustering at q.

k=5 control: G_5,2,2 (q=4) HAS |E*|=0 and IS vertex-critical — so its family DOES
have x=4 as a common root while vertex-critical. Whatever distinguishes the k=4
|E*|=0 non-vertex-critical hosts from this k=5 vertex-critical host is the q=3 lever.
"""
import itertools
import networkx as nx
import sympy as sp
import numpy as np
from forge_verify import is_k_colorable, critical_edges

x = sp.symbols('x')
_CACHE = {}


def circ(n, S):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for i in range(n):
        for s in S:
            G.add_edge(i, (i + s) % n)
    return G


def _count_proper_colorings(G, k):
    """exact #proper k-colorings via backtracking (fast for our sizes)."""
    nodes = list(G.nodes())
    n = len(nodes)
    if n == 0:
        return 1
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [[] for _ in range(n)]
    for u, v in G.edges():
        if u != v:
            adj[idx[u]].append(idx[v]); adj[idx[v]].append(idx[u])
    order = sorted(range(n), key=lambda i: -len(adj[i]))
    color = [-1] * n
    # count via DFS over the order; this is #colorings (not just existence)
    cnt = 0
    def dfs(p):
        nonlocal cnt
        if p == n:
            cnt += 1
            return
        i = order[p]
        used = {color[j] for j in adj[i] if color[j] != -1}
        for c in range(k):
            if c not in used:
                color[i] = c
                dfs(p + 1)
                color[i] = -1
    dfs(0)
    return cnt


class _LocalPoly:
    """Local behavior of P(G,x) at integer points near q — exact integer values
    P(G,k) for small k, used to read off root-at-q (P(q)=0) and the local
    derivative/sign structure via finite differences. Avoids the full polynomial."""
    def __init__(self, vals):
        self.vals = vals  # dict k -> P(G,k) for k in 0..6
    def eval(self, q):
        return self.vals[q]
    def finite_diffs_at(self, q):
        """forward finite differences at q: approximate scaled derivatives.
        Returns (P(q), P(q+1)-P(q), second diff) — sign structure around q."""
        v = self.vals
        d0 = v[q]
        d1 = v.get(q + 1, 0) - v[q]
        d2 = v.get(q + 2, 0) - 2 * v.get(q + 1, 0) + v[q]
        dm1 = v[q] - v.get(q - 1, 0)
        return d0, d1, d2, dm1


def cp(G, want_counts=True):
    """Local chromatic-poly values P(G,k), k=0..6 (k up to q+2). Counting is
    exponential; only do it when want_counts and n is small enough."""
    n = G.number_of_nodes()
    key = (nx.weisfeiler_lehman_graph_hash(G), want_counts)
    if key in _CACHE:
        return _CACHE[key]
    if want_counts and n <= 13:
        vals = {k: _count_proper_colorings(G, k) for k in range(0, 7)}
    else:
        # large graph: only the load-bearing value P(G,3 or 4) via existence-count
        # surrogate is not available cheaply; mark counts unavailable.
        vals = None
    p = _LocalPoly(vals) if vals is not None else _LocalPoly({})
    _CACHE[key] = p
    return p


def near_q_roots(poly, q, window=1.5):
    """Local root info at integer q from values: x=q is a root iff P(q)=0.
    (Full real-root locations need the polynomial; here we report the local
    integer-point structure, which is what the joint-family lever needs at q.)"""
    return []  # replaced by finite-difference reporting in family_portrait


def family_portrait(G, q, name, sample_edges=None):
    """Portrait of the deleted-edge family {P(G-e,x)} at/near x=q.
    Fast core (any size): for each e, is x=q a ROOT of P(G-e,x)? i.e. is G-e NOT
    q-colorable? P(G-e,q)>0 ⟺ G-e q-colorable ⟺ e is critical (χ drops to q).
    Local structure (small graphs n<=13): finite differences of P at q from exact
    counts P(G-e, q-1..q+2) — gives the LOCAL root multiplicity/sign at q."""
    edges = list(G.edges())
    if sample_edges and len(edges) > sample_edges:
        step = max(1, len(edges) // sample_edges)
        edges = edges[::step]
    n = G.number_of_nodes()
    chi = next((k for k in range(2, 8) if is_k_colorable(G, k)), 8)
    small = n <= 13
    # host: is x=q a root of P(G,x)? (G NOT q-colorable since chi=q+1)
    host_root = not is_k_colorable(G, q)
    n_crit = 0           # e critical: G-e q-colorable (P(G-e,q)>0)
    n_root_at_q = 0      # x=q a root of P(G-e,x): G-e NOT q-colorable (P=0)
    diffs = []           # (P(q), 1st diff, 2nd diff, back-diff) for small graphs
    for (a, b) in edges:
        H = G.copy(); H.remove_edge(a, b)
        crit = is_k_colorable(H, q)   # G-e q-colorable => e critical
        if crit:
            n_crit += 1
        else:
            n_root_at_q += 1
        if small:
            ph = cp(H)
            if ph.vals:
                diffs.append(ph.finite_diffs_at(q))
    all_root_at_q = (n_root_at_q == len(edges))
    print(f"[{name}] n={n} chi={chi} |E|={G.number_of_edges()} (sampled {len(edges)}) "
          f"host x={q} root: {host_root}", flush=True)
    print(f"   family: P(G-e,{q})=0 (x={q} a root, e NON-critical): {n_root_at_q}/{len(edges)}; "
          f"P(G-e,{q})>0 (e critical): {n_crit}/{len(edges)}", flush=True)
    print(f"   x={q} is a COMMON root of the WHOLE sampled family: {all_root_at_q}  "
          f"(this is exactly |E*|=0)", flush=True)
    if diffs:
        # for members where x=q IS a root (d0=0): the 1st forward difference sign
        # tells whether the polynomial is increasing through q (simple root) etc.
        root_members = [d for d in diffs if d[0] == 0]
        nonroot = [d for d in diffs if d[0] != 0]
        if root_members:
            d1s = [d[1] for d in root_members]
            d2s = [d[2] for d in root_members]
            dm1s = [d[3] for d in root_members]
            print(f"   root-at-{q} members ({len(root_members)}): forward-diff P({q}+1)-P({q}) "
                  f"range [{min(d1s)},{max(d1s)}] (all >0 => P rising through {q}); "
                  f"back-diff P({q})-P({q}-1) range [{min(dm1s)},{max(dm1s)}]", flush=True)
            # local multiplicity proxy: if back-diff and fwd-diff both nonzero and
            # opposite/same sign reveals crossing vs touch
            crossing = sum(1 for d in root_members if d[1] * d[3] < 0)
            touching = sum(1 for d in root_members if d[1] * d[3] > 0)
            print(f"   local at {q}: ~crossing (simple root, P changes sign) {crossing}, "
                  f"~touching (even mult) {touching} of {len(root_members)}", flush=True)
        if nonroot:
            print(f"   critical members ({len(nonroot)}): P({q})>0 values "
                  f"range [{min(d[0] for d in nonroot)},{max(d[0] for d in nonroot)}]", flush=True)
    return {"name": name, "n": n, "chi": chi, "q": q, "n_crit": n_crit,
            "n_root_at_q": n_root_at_q, "all_root_at_q": all_root_at_q}


if __name__ == "__main__":
    print("=== FAMILY PORTRAITS near x=3 (k=4 targets) ===\n", flush=True)

    # 1. cocktail crux K_{2,2,2,2} (|E*|=0, NOT vertex-critical)
    K2222 = nx.complete_multipartite_graph(2, 2, 2, 2)
    family_portrait(nx.convert_node_labels_to_integers(K2222), 3, "K_{2,2,2,2} cocktail (|E*|=0, not-vc)")
    print()

    # 2. K(6,2) Kneser (|E*|=0, 6-regular, NOT vertex-critical)
    def kneser(n, k):
        V = list(itertools.combinations(range(n), k)); G = nx.Graph(); G.add_nodes_from(V)
        for a, b in itertools.combinations(V, 2):
            if not (set(a) & set(b)): G.add_edge(a, b)
        return nx.convert_node_labels_to_integers(G)
    family_portrait(kneser(6, 2), 3, "K(6,2) Kneser (|E*|=0, not-vc)", sample_edges=20)
    print()

    # 3. an n=8 |E*|=0 chi=4 graph (GCZvv{) — NOT vertex-critical
    family_portrait(nx.from_graph6_bytes("GCZvv{".encode()), 3, "n8 |E*|=0 GCZvv{ (not-vc)")
    print()

    # 4. a VERTEX-CRITICAL host with critical edges: n=10 champion (|E*|=8)
    family_portrait(nx.from_graph6_bytes("ICpdbY{]_".encode()), 3, "n10 champion (vc, |E*|=8)")
    print()

    # 5. C_13(1,2,5) — vertex-critical, |E*|=13 (the n=13 extremal near-miss)
    family_portrait(circ(13, {1, 2, 5}), 3, "C13(1,2,5) extremal (vc, |E*|=13)", sample_edges=20)
    print()

    print("=== k=5 CONTROL: G_5,2,2 family near x=4 (q=4) — MUST break the k=4 pattern ===\n", flush=True)
    # G_5,2,2: circulant Z_17 {1,3,4,5}, chi=5, vertex-critical, |E*|=0 (the escape)
    family_portrait(circ(17, {1, 3, 4, 5}), 4, "G_5,2,2 (q=4, vc, |E*|=0) CONTROL", sample_edges=20)
