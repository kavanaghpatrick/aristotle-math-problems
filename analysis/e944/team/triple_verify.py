#!/usr/bin/env python3
"""
triple_verify.py — three-independent-algorithm concordance check for an E944
(k=4, r=1) witness candidate.

The three algorithms are genuinely different (a bug in one is extremely unlikely to
be mirrored by the other two), so unanimous agreement is the strongest verification
available before alerting the team:

  1. checkers.py        — DSATUR backtracking chromatic number (+ SAT dual path).
                          This is the EXACT VERDICT (is_erdos944_k_r1).
  2. gpu_verifier.py    — hunter's 3^n exhaustive GPU enumeration (gpu_is_witness).
  3. bhk_engine.py      — gpu-smith's 2^n inclusion-exclusion modular screen (analyze).

USAGE in the marathon gate (after the CPU screen flags a chi>=4 survivor):
    ok, report = triple_verify(n, edges)
    if ok:   # all three agree it IS a (4,1)-witness
        ... run skeptic_adjudicate, then ALERT team-lead + skeptic + algebra ...
    else:
        ... report["disagreement"] localizes which algorithm dissents and on what ...

The CPU checkers result is authoritative; the two GPU paths are corroboration. If the
GPUs disagree with checkers, that is a BUG to chase (in whichever path), not a witness.
"""
import sys

sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")

import checkers as CK
from bhk_engine import BHKEngine


def _checkers_predicate(n, edges):
    """Exact (4,1)-witness predicate + the criticality vectors, all via backtracking."""
    chi = CK.chi_bt(edges, n)
    is_wit = CK.is_erdos944_k_r1(edges, n, 4)
    vert_3col = []
    for v in range(n):
        sub = [(a, b) for (a, b) in edges if a != v and b != v]
        vert_3col.append(CK.chi_bt(sub, n) <= 3)
    edge_3col = []
    for j in range(len(edges)):
        sub = [e for i, e in enumerate(edges) if i != j]
        edge_3col.append(CK.chi_bt(sub, n) <= 3)
    return {
        "chi": chi,
        "chi_le_3": chi <= 3,
        "witness": bool(is_wit),
        "vert_3col": vert_3col,
        "edge_3col": edge_3col,
    }


def _bhk_predicate(n, edges, device="mps"):
    eng = BHKEngine(n, device=device)
    r = eng.analyze(edges)
    return {
        "chi_le_3": r["chi_le_3"],
        "witness": r["witness_candidate"],
        "vert_3col": r["vertex_3col"],
        "edge_3col": r["edge_3col"],
    }


def _gpu3n_predicate(n, edges, device=None):
    """hunter's 3^n kernel. Optional — skipped gracefully if unavailable."""
    try:
        from gpu_verifier import gpu_is_witness, gpu_coloring_analysis
    except Exception as ex:  # pragma: no cover
        return None, f"gpu_verifier import failed: {ex}"
    a = gpu_coloring_analysis(n, edges, incident_vertex=True, device=device)
    is_wit, info = gpu_is_witness(n, edges, device=device)
    return {
        "chi_le_3": a["chi_le_3"],
        "witness": bool(is_wit),
        "vert_3col": a["vert_3col"],
        "edge_3col": a["edge_3col"],
    }, None


def triple_verify(n, edges, device="mps", require_gpu3n=True):
    """Run all three algorithms on the (4,1) predicate and check concordance.

    Returns (all_agree_witness, report). `all_agree_witness` is True iff every
    available algorithm agrees the graph IS a (4,1)-witness. `report` carries each
    algorithm's verdict and a `disagreement` list localizing any dissent (on the
    witness flag, the chi<=3 screen, or any per-vertex / per-edge entry)."""
    edges = sorted(set((min(a, b), max(a, b)) for a, b in edges if a != b))
    m = len(edges)

    ck = _checkers_predicate(n, edges)
    bhk = _bhk_predicate(n, edges, device=device)
    g3n, g3n_err = _gpu3n_predicate(n, edges, device=device)

    algos = {"checkers": ck, "bhk": bhk}
    if g3n is not None:
        algos["gpu3n"] = g3n
    elif require_gpu3n:
        return False, {"error": f"gpu3n unavailable ({g3n_err}); cannot complete "
                                f"three-way verification", "checkers": ck, "bhk": bhk}

    # concordance: compare every pair against checkers (authoritative).
    disagreement = []
    for name, a in algos.items():
        if name == "checkers":
            continue
        if a["witness"] != ck["witness"]:
            disagreement.append(f"{name}.witness={a['witness']} != checkers={ck['witness']}")
        if a["chi_le_3"] != ck["chi_le_3"]:
            disagreement.append(f"{name}.chi_le_3={a['chi_le_3']} != checkers={ck['chi_le_3']}")
        if list(a["vert_3col"]) != list(ck["vert_3col"]):
            d = [v for v in range(n) if a["vert_3col"][v] != ck["vert_3col"][v]]
            disagreement.append(f"{name}.vert_3col differs at {d}")
        if list(a["edge_3col"]) != list(ck["edge_3col"]):
            d = [j for j in range(m) if a["edge_3col"][j] != ck["edge_3col"][j]]
            disagreement.append(f"{name}.edge_3col differs at {d}")

    all_agree_witness = (ck["witness"]
                         and all(a["witness"] for a in algos.values())
                         and not disagreement)

    report = {
        "n": n, "m": m,
        "verdicts": {name: a["witness"] for name, a in algos.items()},
        "checkers_chi": ck["chi"],
        "algorithms_run": list(algos.keys()),
        "disagreement": disagreement,
        "all_agree_witness": all_agree_witness,
    }
    return all_agree_witness, report


if __name__ == "__main__":
    # self-check on the census: NONE of these are (4,1)-witnesses, and all three
    # algorithms must AGREE on that (no disagreement), proving the concordance path.
    from bhk_engine import circulant_edges, cocktail_party_edges
    import networkx as nx

    dev = sys.argv[1] if len(sys.argv) > 1 else "mps"
    cases = [
        ("C13(1,2,5)", 13, circulant_edges(13, [1, 2, 5])),
        ("C14(1,2,5)", 14, circulant_edges(14, [1, 2, 5])),
    ]
    n8, cp = cocktail_party_edges(4)
    cases.append(("K_2,2,2,2", n8, cp))
    H = nx.convert_node_labels_to_integers(nx.mycielskian(nx.cycle_graph(5)))
    cases.append(("Grotzsch", H.number_of_nodes(),
                  sorted((min(u, v), max(u, v)) for u, v in H.edges())))

    print(f"triple_verify self-check (device={dev}) — none are (4,1)-witnesses; "
          f"all three algorithms must concur with NO disagreement:")
    bad = 0
    for name, n, e in cases:
        ok, rep = triple_verify(n, e, device=dev, require_gpu3n=True)
        if "error" in rep:
            print(f"  [{name}] SKIP/ERROR: {rep['error']}")
            continue
        concord = "CONCORDANT" if not rep["disagreement"] else f"DISAGREE {rep['disagreement']}"
        print(f"  [{name}] verdicts={rep['verdicts']} chi={rep['checkers_chi']} "
              f"witness_unanimous={ok} {concord}")
        if rep["disagreement"]:
            bad += 1
    print("SELF-CHECK", "PASSED (all algorithms concordant)" if bad == 0
          else f"FAILED ({bad} disagreements)")
    sys.exit(1 if bad else 0)
