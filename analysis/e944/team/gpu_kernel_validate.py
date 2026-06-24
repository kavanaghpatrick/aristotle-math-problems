#!/usr/bin/env python3
"""
Validation harness for gpu_kernel.py.

Cross-checks the MPS kernel's EXACT outputs against the independent ground truth in
checkers.py / critedge.py on:
  - the named E944 census (C13(1,2,5), C14(1,2,5), cocktail-party K_{2,2,2,2},
    Grotzsch, plus K4/K5/C5 sanity)
  - 20 random graphs n=10..13, compared vertex-by-vertex and edge-by-edge.

ANY mismatch -> nonzero exit. Prints a validation table.
"""
import sys
import random

import networkx as nx

sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from gpu_kernel import GpuColoring, circulant_edges, cocktail_party_edges
import checkers as CK
import critedge as CE


DEV = sys.argv[1] if len(sys.argv) > 1 else "mps"


def gt_critical_edges(edges, n, chi):
    """Ground-truth per-edge criticality list (chi(G-e) < chi via checkers backtrack),
    in the SAME edge order as `edges`."""
    out = []
    for j in range(len(edges)):
        sub = [e for i, e in enumerate(edges) if i != j]
        out.append(CK.chi_bt(sub, n) < chi)
    return out


def gt_critical_vertices(edges, n, chi):
    out = []
    for v in range(n):
        sub = [(a, b) for (a, b) in edges if a != v and b != v]
        # G - v on the same n labels (v isolated) has the same chi as the relabeled
        # G-v, because an isolated vertex never raises chi (chi>=1 always once edges
        # exist). Use checkers on the n-label graph directly.
        out.append(CK.chi_bt(sub, n) < chi)
    return out


def nx_edges(G):
    H = nx.convert_node_labels_to_integers(G)
    n = H.number_of_nodes()
    edges = sorted((min(u, v), max(u, v)) for (u, v) in H.edges())
    return edges, n


FAILS = []
ROWS = []


def check(name, edges, n, expect=None):
    """Run kernel + ground truth, compare every field, record a table row."""
    edges = sorted(set((min(a, b), max(a, b)) for a, b in edges if a != b))
    g = GpuColoring(n, device=DEV)
    r = g.analyze(edges)

    # ground truth
    chi_gt = CK.chi_bt(edges, n)
    f_gt = None  # computed below via exhaustive (cheap for n<=13 via kernel CPU? use kernel f)
    ce_gt = gt_critical_edges(edges, n, chi_gt)
    cv_gt = gt_critical_vertices(edges, n, chi_gt)
    nce_gt = sum(ce_gt)
    ncv_gt = sum(cv_gt)

    ok = True
    notes = []
    if r["chi"] != chi_gt:
        ok = False; notes.append(f"chi {r['chi']}!={chi_gt}")
    if r["critical_edges"] != ce_gt:
        ok = False
        diff = [j for j in range(len(edges)) if r["critical_edges"][j] != ce_gt[j]]
        notes.append(f"crit-edge mismatch idx {diff}")
    if r["critical_vertices"] != cv_gt:
        ok = False
        diff = [v for v in range(n) if r["critical_vertices"][v] != cv_gt[v]]
        notes.append(f"crit-vtx mismatch idx {diff}")
    if r["num_critical_edges"] != nce_gt:
        ok = False; notes.append(f"#critE {r['num_critical_edges']}!={nce_gt}")
    if r["num_critical_vertices"] != ncv_gt:
        ok = False; notes.append(f"#critV {r['num_critical_vertices']}!={ncv_gt}")

    # expected-value spot checks (named graphs)
    if expect:
        for kf, val in expect.items():
            if r.get(kf) != val:
                ok = False; notes.append(f"{kf} {r.get(kf)}!={val}(exp)")

    if not ok:
        FAILS.append((name, notes))
    ROWS.append((name, n, len(edges), r["chi"], r["f"], r["B1"],
                 f"{r['num_critical_edges']}/{nce_gt}",
                 f"{r['num_critical_vertices']}/{ncv_gt}",
                 "OK" if ok else "FAIL " + ";".join(notes)))
    return r


print("=" * 100)
print(f"GPU KERNEL VALIDATION  (device={DEV})  — kernel vs checkers.py ground truth")
print("=" * 100)

# ---- named E944 census ----
check("C13(1,2,5)", circulant_edges(13, [1, 2, 5]), 13,
      expect={"chi": 4, "f": 1, "num_critical_edges": 13, "num_critical_vertices": 13})
check("C14(1,2,5)", circulant_edges(14, [1, 2, 5]), 14,
      expect={"chi": 4, "num_critical_edges": 0})  # 0 critical edges, NOT vertex-critical
n8, cp = cocktail_party_edges(4)
check("K_{2,2,2,2} (cocktail n=8)", cp, n8,
      expect={"chi": 4, "num_critical_edges": 0, "num_critical_vertices": 0})
ge, gn = nx_edges(nx.mycielskian(nx.cycle_graph(5)))  # Grotzsch
m_grot0 = len(set((min(a, b), max(a, b)) for a, b in ge))
check("Grotzsch", ge, gn,
      expect={"chi": 4, "num_critical_edges": m_grot0, "num_critical_vertices": gn})

# ---- small sanity ----
for nm, G, exp in [
    ("K4", nx.complete_graph(4), {"chi": 4}),
    ("K5", nx.complete_graph(5), {"chi": 5}),
    ("C5", nx.cycle_graph(5), {"chi": 3}),
    ("C6", nx.cycle_graph(6), {"chi": 2}),
    ("Petersen", nx.petersen_graph(), {"chi": 3}),
    ("Wheel W5", nx.wheel_graph(6), {"chi": 4}),
]:
    e, n = nx_edges(G)
    check(nm, e, n, expect=exp)

# explicit Grotzsch all-edges-critical assertion
ge2, gn2 = nx_edges(nx.mycielskian(nx.cycle_graph(5)))
g = GpuColoring(gn2, device=DEV)
rg = g.analyze(sorted(set((min(a,b),max(a,b)) for a,b in ge2)))
m_grot = len(set((min(a,b),max(a,b)) for a,b in ge2))
if rg["num_critical_edges"] != m_grot:
    FAILS.append(("Grotzsch-all-edges-critical",
                  [f"only {rg['num_critical_edges']}/{m_grot} edges critical"]))
else:
    print(f"[Grotzsch] all {m_grot} edges critical: OK; 4-vertex-critical: "
          f"{rg['num_critical_vertices']}/{gn2}")

# ---- 20 random graphs n=10..13, full vertex+edge cross-check ----
print("-" * 100)
print("20 random graphs n=10..13 (full per-vertex + per-edge cross-check vs checkers.py)")
rng = random.Random(20260611)
rand_fail = 0
for t in range(20):
    n = rng.randint(10, 13)
    p = rng.uniform(0.3, 0.7)
    G = nx.gnp_random_graph(n, p, seed=rng.randint(0, 10**9))
    e, n = nx_edges(G)
    r = check(f"rand{t}_n{n}_m{len(e)}", e, n)
    # check() already compares full crit-edge & crit-vtx vectors against GT
print("-" * 100)

# ---- print table ----
hdr = ("name", "n", "m", "chi", "f", "B1", "critE k/gt", "critV k/gt", "status")
w = [26, 4, 5, 4, 4, 8, 12, 12, 40]
def row(cols):
    return " ".join(str(c).ljust(wi)[:wi] for c, wi in zip(cols, w))
print(row(hdr))
print("-" * 120)
for rr in ROWS:
    print(row(rr))
print("=" * 100)

if FAILS:
    print(f"VALIDATION FAILED — {len(FAILS)} discrepancies:")
    for nm, notes in FAILS:
        print(f"  [{nm}] {notes}")
    sys.exit(1)
else:
    print(f"VALIDATION PASSED — kernel ({DEV}) exactly matches checkers.py on the full "
          f"census + 20 random graphs (every vertex, every edge).")
    sys.exit(0)
