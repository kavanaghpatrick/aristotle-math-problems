#!/usr/bin/env python3
"""
entropy_neighborhood.py — neighborhood-coloring entropy functional (count + forge).
(E944 entropy lane) — CORRECTED.

CORRECT definitions:
  - v is critical / absorber  ⟺  χ(G−v) < χ(G)  (=k−1). This is THE vertex-critical test.
  - SEPARATELY, the neighborhood-coloring ENTROPY diagnostic: over all proper
    (k−1)-colorings c of G−v, the color-class distribution (a,b,c) of N(v). Define
    H(v) = min over (k−1)-colorings of G−v of (deg(v) − max class size) = min spread.
    Low H(v) = some coloring makes N(v) lopsided (dominant color); high H(v) = N(v)
    is forced balanced in every coloring.

forge's slope lemma: a low-degree vertex (deg ≤ 2(k−1)−1) forces singleton structure
= low spread. The entropy hypothesis: in the f≥2 (no-critical-edge) dense regime, H(v)
is forced HIGH (balanced neighborhoods) — the continuous shadow of absorber suppression.

Controls: k=5 witnesses (G_5,2,2) MUST test vertex-critical=True (absorber everywhere).
For k=5 use (k−1)=4-colorings of G−v.
"""
import sys, os, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
import networkx as nx


def colorings_of_Gminus(g, v, q):
    """All proper q-colorings of G - v. Returns list of dict {u: color}. q = k-1."""
    n = g.n
    others = [u for u in range(n) if u != v]
    adj = g.adj
    col = {}
    res = []
    def ok(u, c):
        nb = adj[u]
        while nb:
            low = nb & (-nb); w = low.bit_length()-1
            if w != v and col.get(w) == c: return False
            nb ^= low
        return True
    def bt(i):
        if i == len(others):
            res.append(dict(col)); return
        u = others[i]
        for c in range(q):
            if ok(u, c):
                col[u] = c; bt(i+1); del col[u]
    bt(0)
    return res


def vertex_entropy(g, v, k, cap=500000):
    """Compute H(v) over (k-1)-colorings of G-v, and whether v is critical.
    v critical ⟺ G-v is (k-1)-colorable ⟺ colorings nonempty."""
    q = k-1
    nbrs = [u for u in range(g.n) if g.has(v,u)]
    d = len(nbrs)
    cols = colorings_of_Gminus(g, v, q)
    critical = len(cols) > 0
    if not critical:
        return {"deg": d, "critical": False, "Hv": None}
    Hv = d
    for col in cols[:cap]:
        cnt = [0]*q
        for u in nbrs: cnt[col[u]] += 1
        spread = d - max(cnt)
        if spread < Hv: Hv = spread
    return {"deg": d, "critical": True, "Hv": Hv}


def analyze_graph(g, label, k):
    chi = chi_exact(g.adj, g.n)
    profs = [vertex_entropy(g, v, k) for v in range(g.n)]
    noncrit = sum(1 for p in profs if not p["critical"])
    vc = (noncrit == 0) and (chi == k)
    Hvals = [p["Hv"] for p in profs if p["Hv"] is not None]
    minH = min(Hvals) if Hvals else None
    maxH = max(Hvals) if Hvals else None
    # normalized entropy: avg H(v)/deg(v) over critical vertices
    norm = [p["Hv"]/p["deg"] for p in profs if p["Hv"] is not None and p["deg"]>0]
    avgnorm = sum(norm)/len(norm) if norm else None
    print(f"  {label} (k={k}, n={g.n}, χ={chi}): vertex-critical={vc}, "
          f"#non-critical-vtx={noncrit}, H(v)∈[{minH},{maxH}], "
          f"avg H/deg={avgnorm:.3f}" if avgnorm is not None else
          f"  {label} (k={k}, n={g.n}, χ={chi}): vertex-critical={vc}, #non-critical={noncrit}")
    return {"label":label,"k":k,"vc":vc,"noncrit":noncrit,"minH":minH,"maxH":maxH,"avgnorm":avgnorm}


def g6_to_graph(g6):
    G = nx.from_graph6_bytes(g6.encode())
    nodes=list(G.nodes()); idx={x:i for i,x in enumerate(nodes)}
    return Graph(len(nodes), [(idx[a],idx[b]) for a,b in G.edges()])


def main():
    pkg = json.load(open(os.path.join(os.path.dirname(__file__),'forge_structural_package.json')))
    labels = {10:"n10-champ(k4,|E*|=8)", 13:"C13(1,2,5)(k4,|E*|=13)",
              14:"C14(1,2,5)(k4,|E*|=0,not-vc)", 15:"k4-n15",
              17:"G_5,2,2(k5 WITNESS)", 8:"k4-n8"}
    print("=== Neighborhood entropy H(v): critical test + N(v) color-spread ===")
    print("witness needs vc=True AND f≥2; H(v)=min N(v) spread; k=5 controls MUST be vc.\n")
    results=[]
    for s in pkg:
        n=s.get("n"); g6=s.get("g6")
        if not g6: continue
        if n and n>=18:
            print(f"  (skip n={n}: 4-coloring enum of G-v infeasible for k=5 large)"); continue
        try: g=g6_to_graph(g6)
        except Exception as e: print(f"  ({g6[:8]} parse fail)"); continue
        k = 5 if n==17 else 4
        results.append(analyze_graph(g, labels.get(n,f"n{n}"), k))
    print("\n=== SUMMARY (does H/deg separate witnesses from non-witnesses?) ===")
    for r in results:
        an = f"{r['avgnorm']:.3f}" if r['avgnorm'] is not None else "n/a"
        print(f"  {r['label']:32s}: vc={r['vc']}, H∈[{r['minH']},{r['maxH']}], avg H/deg={an}")


if __name__ == "__main__":
    main()
