"""
Independent verification of forge's E*-DEGREE SLOPE lemma (jensen, on harness.py):

  LEMMA: in a 4-vertex-critical graph, every vertex v has
         E*-deg(v) ≥ max(0, 6 − deg(v)),
  where E*-deg(v) = # critical edges incident to v.

Proof (forge): v critical ⟹ G−v is 3-colorable; χ(G)=4 ⟹ in any 3-coloring of G−v,
N(v) meets all 3 colors (else v extends, χ=3); so the deg(v) neighbors split into 3
NONEMPTY color classes. The minimum number of SINGLETON classes over partitions of
deg(v) into 3 nonempty parts is max(0, 6−deg(v)) [d=3→(1,1,1):3; d=4→(2,1,1):2;
d=5→(2,2,1):1; d≥6→(2,2,2):0]. A neighbor u alone in its class ⟹ the edge uv is
critical (recolor u to a free color in G−v−uv... per the per-vertex criticality lemma).
So ≥ max(0,6−deg(v)) incident edges are critical. ∎

We verify E*-deg(v) ≥ max(0,6−deg(v)) for EVERY vertex of EVERY 4-vertex-critical
graph we can enumerate/build, counting violations (must be 0). Independent of forge's
checker (uses harness.py's 2-engine χ). Pushes to larger n via known 4-vc graphs +
the n≤7 atlas census.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def estar_deg(G):
    """Return dict v -> #critical edges incident to v."""
    ce = critical_edges(G)
    d = {v: 0 for v in G.nodes()}
    for (u, v) in ce:
        d[u] += 1; d[v] += 1
    return d


def check_slope(G, name, verbose=False):
    """Verify E*-deg(v) >= max(0, 6-deg(v)) for all v. Returns (#vertices, #violations)."""
    if chromatic_number(G) != 4 or not is_vertex_critical(G, 4):
        return None
    ed = estar_deg(G)
    viol = 0
    tight = 0
    for v in G.nodes():
        dv = G.degree(v)
        bound = max(0, 6 - dv)
        if ed[v] < bound:
            viol += 1
            if verbose:
                print(f"  VIOLATION {name} v={v}: deg={dv} E*-deg={ed[v]} < bound {bound}")
        elif ed[v] == bound and bound > 0:
            tight += 1
    return (G.number_of_nodes(), viol, tight)


def atlas_4vc(nmax=7):
    """All 4-vertex-critical graphs up to nmax via graph_atlas_g (complete to n=7)."""
    from networkx.generators.atlas import graph_atlas_g
    out = []
    for G in graph_atlas_g():
        if 1 <= G.number_of_nodes() <= nmax and G.number_of_nodes() >= 4:
            if chromatic_number(G) == 4 and is_vertex_critical(G, 4):
                out.append(G)
    return out


if __name__ == "__main__":
    total_v = 0; total_viol = 0; total_tight = 0; total_g = 0
    print("=== Verifying forge's E*-slope lemma: E*-deg(v) ≥ max(0,6-deg(v)) ===")
    print("-- census n≤7 (atlas, complete) --", flush=True)
    for G in atlas_4vc(7):
        r = check_slope(G, f"atlas_n{G.number_of_nodes()}", verbose=True)
        if r:
            nv, vi, ti = r
            total_v += nv; total_viol += vi; total_tight += ti; total_g += 1
    print(f"  census n≤7: {total_g} graphs, {total_v} vertices, {total_viol} violations, {total_tight} tight", flush=True)

    print("-- larger known 4-vc graphs (push toward n≥31) --", flush=True)
    big = {
        "Grotzsch(11)": nx.mycielskian(nx.cycle_graph(5)),
        "C13(1,2,5)": nx.circulant_graph(13, [1, 2, 5]),
        "C16(1,2,5)": nx.circulant_graph(16, [1, 2, 5]),
        "C19(1,2,5)": nx.circulant_graph(19, [1, 2, 5]),
        "C25(1,2,5)": nx.circulant_graph(25, [1, 2, 5]),
        "C31(1,2,5)": nx.circulant_graph(31, [1, 2, 5]),
        "Myc(Grotzsch)=23": nx.mycielskian(nx.mycielskian(nx.cycle_graph(5))),
    }
    for name, G in big.items():
        r = check_slope(G, name, verbose=True)
        if r is None:
            print(f"  {name}: not 4-vertex-critical (skip)", flush=True)
        else:
            nv, vi, ti = r
            total_v += nv; total_viol += vi; total_tight += ti
            print(f"  {name}: n={nv}, violations={vi}, tight-vertices={ti}", flush=True)

    # also load wall's n=19,23 seeds
    import json
    try:
        seeds = json.load(open("analysis/e944/team/wall5_plateau_seeds_n19_n23.json"))
        for s in seeds:
            G = nx.Graph(); G.add_edges_from(tuple(e) for e in s["edges"])
            r = check_slope(G, s["label"], verbose=True)
            if r:
                nv, vi, ti = r
                total_v += nv; total_viol += vi
                print(f"  {s['label']}: n={nv}, violations={vi}, tight={ti}", flush=True)
    except Exception as e:
        print(f"  (wall seeds not loaded: {e})")

    print(f"\nTOTAL: {total_v} vertices checked, {total_viol} VIOLATIONS of E*-deg≥max(0,6-deg).", flush=True)
    print("LEMMA HOLDS" if total_viol == 0 else "LEMMA VIOLATED — investigate!", flush=True)
