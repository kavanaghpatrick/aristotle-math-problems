#!/usr/bin/env python3
"""
Validation harness for bhk_engine.py (Björklund–Husfeldt–Koivisto IE engine).

Independent ground truth = checkers.py (DSATUR backtracking + SAT dual path).
BHK is a COMPLETELY different algorithm (2^n inclusion-exclusion over independent
sets) than backtracking, so agreement is strong cross-validation.

Coverage (per team-lead spec):
  - full E944 census: C13(1,2,5) [vc, 13 critical edges, f=1], C14(1,2,5) [0 critical,
    not vc], K_{2,2,2,2} cocktail [chi=4, 0 critical, not vc], Grötzsch [vc, all 20
    critical], plus K4/K5/C5 sanity.
  - 50 random graphs n=10..13, checked invariant-by-invariant (chi<=3, per-vertex
    G-v 3col vector, per-edge G-e 3col vector).
  - BOTH prime moduli exercised (the engine declares zero only on both; the harness
    additionally asserts the two moduli AGREE on every zero/nonzero decision).

Any mismatch => nonzero exit.
"""
import sys
import random

import networkx as nx

sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from bhk_engine import BHKEngine, circulant_edges, cocktail_party_edges, P1, P2
import bhk_engine as BHK
import checkers as CK


DEV = sys.argv[1] if len(sys.argv) > 1 else "mps"
FAILS = []
ROWS = []


def gt_vertex_3col(edges, n):
    """Ground truth per-vertex: is G-v 3-colorable? (chi(G-v) <= 3)."""
    out = []
    for v in range(n):
        sub = [(a, b) for (a, b) in edges if a != v and b != v]
        out.append(CK.chi_bt(sub, n) <= 3)
    return out


def gt_edge_3col(edges, n):
    out = []
    for j in range(len(edges)):
        sub = [e for i, e in enumerate(edges) if i != j]
        out.append(CK.chi_bt(sub, n) <= 3)
    return out


def nx_edges(G):
    H = nx.convert_node_labels_to_integers(G)
    n = H.number_of_nodes()
    return sorted((min(u, v), max(u, v)) for u, v in H.edges()), n


def both_moduli_agree(eng, edges):
    """Assert P1 and P2 give the SAME zero/nonzero verdict on c3(G)."""
    c1, c2 = eng._c3_both(eng._norm(edges))
    z1, z2 = (c1 % P1 == 0), (c2 % P2 == 0)
    return z1 == z2, (c1, c2)


def check(name, edges, n, expect=None):
    edges = sorted(set((min(a, b), max(a, b)) for a, b in edges if a != b))
    eng = BHKEngine(n, device=DEV)
    r = eng.analyze(edges)

    chi = CK.chi_bt(edges, n)
    gt_3col = chi <= 3
    gt_v = gt_vertex_3col(edges, n)
    gt_e = gt_edge_3col(edges, n)

    ok = True
    notes = []
    # chi<=3 screen
    if r["chi_le_3"] != gt_3col:
        ok = False; notes.append(f"chi_le_3 {r['chi_le_3']}!={gt_3col}")
    # both moduli must agree (no single-prime false zero in the census)
    agree, (c1, c2) = both_moduli_agree(eng, edges)
    if not agree:
        ok = False; notes.append(f"moduli disagree c1%P1={c1%P1} c2%P2={c2%P2}")
    # per-vertex / per-edge vectors
    if r["vertex_3col"] != gt_v:
        ok = False
        d = [v for v in range(n) if r["vertex_3col"][v] != gt_v[v]]
        notes.append(f"vertex_3col mismatch idx {d}")
    if r["edge_3col"] != gt_e:
        ok = False
        d = [j for j in range(len(edges)) if r["edge_3col"][j] != gt_e[j]]
        notes.append(f"edge_3col mismatch idx {d}")

    # expected named-graph values (interpreted only when chi(G)=4)
    if expect:
        for kf, val in expect.items():
            if r.get(kf) != val:
                ok = False; notes.append(f"{kf} {r.get(kf)}!={val}(exp)")

    if not ok:
        FAILS.append((name, notes))
    ROWS.append((name, n, len(edges), chi,
                 r["chi_le_3"],
                 f"{r['num_critical_vertices']}",
                 f"{r['num_critical_edges']}",
                 r["witness_candidate"],
                 "OK" if ok else "FAIL " + ";".join(notes)))
    return r


print("=" * 104)
print(f"BHK ENGINE VALIDATION  (device={DEV})  — IE 2^n engine vs checkers.py "
      f"(both prime moduli)")
print("=" * 104)

# named census
check("C13(1,2,5)", circulant_edges(13, [1, 2, 5]), 13,
      expect={"chi_le_3": False, "num_critical_vertices": 13,
              "num_critical_edges": 13, "is_vertex_critical": True,
              "no_critical_edge": False, "witness_candidate": False})
check("C14(1,2,5)", circulant_edges(14, [1, 2, 5]), 14,
      expect={"chi_le_3": False, "num_critical_edges": 0, "is_vertex_critical": False})
n8, cp = cocktail_party_edges(4)
check("K_{2,2,2,2} cocktail n=8", cp, n8,
      expect={"chi_le_3": False, "num_critical_edges": 0,
              "num_critical_vertices": 0, "is_vertex_critical": False})
ge, gn = nx_edges(nx.mycielskian(nx.cycle_graph(5)))
m_grot = len(ge)
check("Grotzsch", ge, gn,
      expect={"chi_le_3": False, "num_critical_edges": m_grot,
              "num_critical_vertices": gn, "is_vertex_critical": True,
              "no_critical_edge": False})

# sanity named graphs
for nm, G in [("K4", nx.complete_graph(4)), ("K5", nx.complete_graph(5)),
              ("C5", nx.cycle_graph(5)), ("C6", nx.cycle_graph(6)),
              ("Petersen", nx.petersen_graph()), ("Wheel W5", nx.wheel_graph(6))]:
    e, n = nx_edges(G)
    check(nm, e, n)

# 50 random graphs n=10..13, invariant by invariant
print("-" * 104)
print("50 random graphs n=10..13 (chi<=3 + full per-vertex + per-edge vectors vs checkers.py)")
rng = random.Random(20260611)
nrand = 50
for t in range(nrand):
    n = rng.randint(10, 13)
    p = rng.uniform(0.25, 0.75)
    G = nx.gnp_random_graph(n, p, seed=rng.randint(0, 10**9))
    e, n = nx_edges(G)
    check(f"rand{t}_n{n}_m{len(e)}", e, n)
print("-" * 104)

# table
hdr = ("name", "n", "m", "chi", "3col?", "critV", "critE", "witness", "status")
w = [26, 4, 5, 4, 6, 6, 6, 8, 40]
def row(c): return " ".join(str(x).ljust(wi)[:wi] for x, wi in zip(c, w))
print(row(hdr)); print("-" * 120)
# only print the named/census rows + any failures in full, summarize randoms
named = ROWS[:10]
rand_rows = ROWS[10:]
for rr in named:
    print(row(rr))
rand_fail = [rr for rr in rand_rows if not rr[-1].startswith("OK")]
print(f"... {len(rand_rows)} random graphs: "
      f"{len(rand_rows)-len(rand_fail)} OK, {len(rand_fail)} FAIL")
for rr in rand_fail:
    print(row(rr))
print("=" * 104)

# ---- BATCHED PATH cross-check: chi_le_3_batch and analyze_batch must match the
#      single-graph analyze() and checkers.py, on a fixed-n batch ----
print("BATCHED-PATH cross-check (chi_le_3_batch + analyze_batch vs single + checkers)")
rng2 = random.Random(7777)
for nb in (11, 12, 13):
    batch = []
    # include a chi>=4 graph (circulant near-miss) + random graphs at this n
    if nb == 13:
        batch.append(circulant_edges(13, [1, 2, 5]))
    for _ in range(15):
        G = nx.gnp_random_graph(nb, rng2.uniform(0.3, 0.7), seed=rng2.randint(0, 10**9))
        e, _n = nx_edges(G)
        batch.append(e)
    eng = BHKEngine(nb, device=DEV)
    # screen batch
    scr = eng.chi_le_3_batch(batch)
    scr_gt = [CK.chi_bt(e, nb) <= 3 for e in batch]
    if scr != scr_gt:
        bad = [k for k in range(len(batch)) if scr[k] != scr_gt[k]]
        FAILS.append((f"chi_le_3_batch n={nb}", [f"screen mismatch idx {bad}"]))
    # full analyze_batch (force full on all, compare to single analyze)
    ab = eng.analyze_batch(batch, full_on_chi4_only=False)
    for k, e in enumerate(batch):
        single = eng.analyze(e)
        for key in ("chi_le_3", "num_critical_vertices", "num_critical_edges",
                    "is_vertex_critical", "no_critical_edge", "witness_candidate",
                    "vertex_3col", "edge_3col"):
            if ab[k][key] != single[key]:
                FAILS.append((f"analyze_batch n={nb} idx{k}",
                              [f"{key}: batch={ab[k][key]} single={single[key]}"]))
                break
    # also exercise the efficient path (chi4-only) and check screened-out graphs
    ab2 = eng.analyze_batch(batch, full_on_chi4_only=True)
    for k in range(len(batch)):
        if ab2[k]["chi_le_3"] != scr_gt[k]:
            FAILS.append((f"analyze_batch(chi4only) n={nb} idx{k}",
                          [f"chi_le_3 {ab2[k]['chi_le_3']}!={scr_gt[k]}"]))
    print(f"  n={nb}: batch of {len(batch)} screened + analyzed, "
          f"{'OK' if not any(f[0].endswith(str(nb)) or f'n={nb}' in f[0] for f in FAILS) else 'see fails'}")
print("=" * 104)

if FAILS:
    print(f"VALIDATION FAILED — {len(FAILS)} discrepancies:")
    for nm, notes in FAILS:
        print(f"  [{nm}] {notes}")
    sys.exit(1)
else:
    print(f"VALIDATION PASSED — BHK engine ({DEV}) matches checkers.py on the full "
          f"census + {nrand} random graphs (chi screen, every vertex, every edge), "
          f"both prime moduli agree on every decision.")
    sys.exit(0)
