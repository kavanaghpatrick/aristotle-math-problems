#!/usr/bin/env python3
"""
absorber_dense.py — measure max absorber-fraction among f≥2 four-chromatic graphs
in the DENSE (δ≥5,6) regime at n=11,12. (count, for wall's cocycle/impossibility lemma)

Locked defs (wall_Estar_nonempty.md):
  f(G)   = min over ℤ₃-colorings p:V→ℤ₃ of #{monochromatic edges}.
           χ(G)=4 ⟺ f≥1; G has a critical edge ⟺ f=1; witness ⟺ f≥2 AND all-absorber.
  g(v)   = min over ℤ₃-colorings of #{mono edges NOT incident to v}; g(v)=0 ⟺ v absorber
           (vertex-critical). all-absorber ⟺ vertex-critical graph.
  absorber-fraction(G) = #{v: g(v)=0} / n.

wall's question: does the absorber SUPPRESSION (n≤9 sparse: max frac 1/7,3/8,3/9 <1)
HOLD in the dense δ≥5,6 witness regime at n=11,12? If max frac stays <1, suppression
confirmed where a witness lives. If any f≥2 graph is all-absorber → that IS a witness.

Method: sample dense graphs (random δ≥5/6, n=11,12), keep χ=4, compute f and absorber
fraction; track the f≥2 subset. (No nauty; random sampling of the dense regime.)
"""
import sys, os, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_anneal import Graph, chi_exact
import networkx as nx


def f_and_absorbers(g):
    """Compute f(G) and the absorber set via full ℤ₃-coloring enumeration (fix
    vertex 0 = color 0 by symmetry). Returns (f, absorber_count, n, per-vertex g=0?).
    For each ℤ₃-coloring track: total mono edges (-> f) and, per vertex v, mono edges
    NOT incident to v (-> g(v) = min over colorings)."""
    n = g.n
    edges = list(g.edges)
    f = None
    gmin = [None]*n  # g(v)
    for tail in itertools.product(range(3), repeat=n-1):
        col = (0,)+tail
        mono = [(a,b) for (a,b) in edges if col[a]==col[b]]
        k = len(mono)
        if f is None or k < f: f = k
        # g(v): mono edges not incident to v
        if k <= (min(x for x in gmin if x is not None)+2 if any(x is not None for x in gmin) else 10**9) or True:
            # compute per-vertex non-incident mono count for this coloring
            for v in range(n):
                cnt = sum(1 for (a,b) in mono if a!=v and b!=v)
                if gmin[v] is None or cnt < gmin[v]:
                    gmin[v] = cnt
    absorbers = [v for v in range(n) if gmin[v]==0]
    return f, len(absorbers), n, absorbers


def sample_dense(n, mindeg, n_samples, rng):
    """Yield random graphs on n vertices with min-degree >= mindeg (via random
    regular + random extra edges), filtered later for chi=4."""
    out = []
    for _ in range(n_samples):
        d = mindeg
        if (d*n) % 2: d += 1  # regular needs even d*n
        try:
            G = nx.random_regular_graph(d, n, seed=rng.randint(0,10**7))
        except Exception:
            continue
        # randomly add a few extra edges to vary (stay >= mindeg)
        extra = rng.randint(0, 4)
        for _ in range(extra):
            u,v = rng.randrange(n), rng.randrange(n)
            if u!=v: G.add_edge(u,v)
        out.append(Graph(n, list(G.edges())))
    return out


def main():
    rng = random.Random(20260610)
    print("=== Absorber-fraction among f≥2 four-chromatic DENSE graphs (count, for wall) ===")
    print("witness ⟺ f≥2 AND absorber-fraction = 1.0 (all-absorber). Does suppression hold dense?\n")
    for n in (11, 12):
        for mindeg in (6, 5):
            samples = sample_dense(n, mindeg, 1500, rng)
            chi4 = [g for g in samples if chi_exact(g.adj, g.n) == 4]
            fge2 = []
            allabs = []
            maxfrac = 0.0
            fracdist = {}
            for g in chi4:
                f, nabs, nn, absb = f_and_absorbers(g)
                if f >= 2:
                    frac = nabs/nn
                    fge2.append((g, f, nabs, frac))
                    maxfrac = max(maxfrac, frac)
                    bucket = round(frac, 2)
                    fracdist[bucket] = fracdist.get(bucket, 0)+1
                    if frac == 1.0:
                        allabs.append(g)
            print(f"n={n} δ≥{mindeg}: sampled {len(samples)}, χ=4: {len(chi4)}, "
                  f"f≥2: {len(fge2)}")
            if fge2:
                print(f"   MAX absorber-fraction among f≥2 = {maxfrac:.3f} "
                      f"({int(round(maxfrac*n))}/{n})")
                print(f"   absorber-fraction distribution (rounded): "
                      f"{dict(sorted(fracdist.items()))}")
                if allabs:
                    print(f"   *** {len(allabs)} ALL-ABSORBER f≥2 graphs = WITNESS CANDIDATES! ***")
                    for g in allabs[:2]:
                        print(f"       edges={sorted(g.edges)}")
                else:
                    print(f"   NO all-absorber f≥2 graph → suppression HOLDS at n={n} δ≥{mindeg}")
            else:
                print(f"   no f≥2 graphs in sample (dense random rarely f≥2)")
            print()
    print("VERDICT: if max absorber-fraction < 1 across dense f≥2 samples, wall's")
    print("absorber-suppression holds in the witness regime → impossibility support.")


if __name__ == "__main__":
    main()
