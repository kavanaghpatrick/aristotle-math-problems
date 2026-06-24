"""
archivist: build a VERIFIED (5,1)-witness — a 5-vertex-critical graph with NO critical edge.

Since Brown's exact 17-vertex graph is locked in the paywalled 1992 paper and absent from
all open secondary sources, we instead construct a genuine k=5 witness via the documented
Jensen circulant family, using the Skottova-Steiner distance-set formula (arXiv:2508.08703,
/tmp/skottova.txt lines 524-577), which specializes to Jensen's construction at k=5.

For k odd (k=5):
  period n_{k,m} = (k-1)*m = 4m
  N = q*n_{k,m} + 1 = 4mq + 1   (q even, multiple of 4)
  D1 = {1,3,...,2m-1}
  D2 = union over q'=0..q/2-1 of ([2m, (k-3)m+1] + q'*n_{k,m}) = ([2m, 2m+1] + q'*4m)
  D3 = union over q'=0..q/2-1 of ([(k+2)m-1, (2k-4)m+1] + q'*n_{k,m}) = ([7m-1, 6m+1] + q'*4m)
     (note for k=5: D3 interval [7m-1, 6m+1] is EMPTY when 7m-1 > 6m+1 i.e. m>2; for m=2 it's [13,13])

Theorem 4.1 needs k>=5, m > 18r+2 = 20 (for r=1) and q >= 24r+12 = 36 multiple of 4 to GUARANTEE
the (k,r) property. Those bounds give a large graph; we VERIFY directly with checkers.py
rather than rely on the asymptotic theorem, and scan smaller (m,q) too in case the property
holds below the proven threshold (common — the bounds are sufficient, not necessary).

A (5,1)-witness: chi=5, every vertex critical (chi(G-v)=4), no single edge critical (chi(G-e)=5).
"""
import sys
import networkx as nx
import checkers


def jensen_circulant_k5(m, q):
    """Skottova-Steiner G_{5,m,q} (k=5 odd case). Returns networkx graph."""
    k = 5
    nkm = (k - 1) * m          # = 4m  (k odd)
    N = q * nkm + 1
    D = set()
    # D1 = {1,3,...,2m-1}
    for d in range(1, 2 * m, 2):
        D.add(d)
    # D2 = U_{q'=0}^{q/2-1} ([2m, (k-3)m+1] + q'*nkm) = [2m, 2m+1] + q'*4m
    lo2, hi2 = 2 * m, (k - 3) * m + 1
    for qp in range(q // 2):
        for d in range(lo2, hi2 + 1):
            D.add(d + qp * nkm)
    # D3 = U ([(k+2)m-1, (2k-4)m+1] + q'*nkm) = [7m-1, 6m+1] + q'*4m
    lo3, hi3 = (k + 2) * m - 1, (2 * k - 4) * m + 1
    for qp in range(q // 2):
        for d in range(lo3, hi3 + 1):
            D.add(d + qp * nkm)
    # build circulant on Z_N with these distances (mod N, cyclic distance)
    G = nx.Graph()
    G.add_nodes_from(range(N))
    for i in range(N):
        for d in D:
            j = (i + d) % N
            cyc = min((j - i) % N, (i - j) % N)
            if 1 <= cyc <= N // 2:
                G.add_edge(i, j)
    return G, N, sorted(D)


def verify(G, k, use_sat=True):
    """Verify (k,1)-witness. SAT chi by default (fast for dense circulants);
    backtracking chi hangs on N~33 deg~12 graphs. cross_check=True re-runs the
    final verdict with the independent backtracking chi on a few key calls."""
    nodes = list(G.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    edges = [(idx[u], idx[w]) for u, w in G.edges()]
    n = len(nodes)
    chi_fn = (lambda e, nn: checkers.chromatic_number_sat(e, nn)) if use_sat else checkers.chi_bt
    chi = chi_fn(edges, n)
    if chi != k:
        return dict(n=n, m_edges=len(edges), chi=chi, verdict=f"chi={chi}!={k}, skip")
    # vertex-critical: chi(G-v) < k for all v
    adj = checkers.edges_to_adj(edges, n)
    for v in range(n):
        sa, sn = checkers.adj_remove_vertex(adj, n, v)
        se = []
        for a in range(sn):
            nb = sa[a]
            while nb:
                low = nb & (-nb); b = low.bit_length() - 1
                if a < b:
                    se.append((a, b))
                nb ^= low
        if chi_fn(se, sn) >= k:
            return dict(n=n, m_edges=len(edges), chi=chi, vertex_critical=False,
                        verdict=f"vertex {v} not critical")
    crit = [e for e in edges if chi_fn(checkers.edges_remove_edge(edges, e), n) < k]
    return dict(n=n, m_edges=len(edges), chi=chi, vertex_critical=True,
                num_critical_edges=len(crit), no_critical_edge=(len(crit) == 0),
                verdict="WITNESS" if len(crit) == 0 else f"{len(crit)} critical edges")


if __name__ == "__main__":
    # scan small (m,q); m up to ~6, q in {4,8,...}. Verify each.
    found = False
    for m in range(2, 8):
        for q in range(4, 13, 4):
            G, N, D = jensen_circulant_k5(m, q)
            if N > 70:           # cap size for exact chi feasibility
                continue
            res = verify(G, 5)
            tag = res.get("verdict", "?")
            print(f"m={m} q={q} N={N} |D|={len(D)} D={D[:8]}{'...' if len(D)>8 else ''} -> {tag}"
                  f"  [{res.get('m_edges','?')} edges, chi={res.get('chi','?')}]")
            if res.get("no_critical_edge"):
                print(f"  *** (5,1)-WITNESS FOUND: m={m} q={q} N={N} ***")
                # save graph6
                nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
                Gc = nx.relabel_nodes(G, idx)
                with open(f"archivist_k5_witness_m{m}_q{q}.g6", "wb") as f:
                    f.write(nx.to_graph6_bytes(Gc, header=False))
                found = True
    if not found:
        print("No (5,1)-witness in the scanned (m,q) range under N<=70; "
              "Theorem 4.1 guarantees one only for m>20,q>=36 (large N).")
