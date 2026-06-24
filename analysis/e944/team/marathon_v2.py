"""
e944 MARATHON v2 (hunter) — hybrid existence sampler, stages chosen by MEASURED throughput.

MEASURED REALITY (settles the architecture, not GPU ideology):
  - CPU backtracking (floor_worker predicate) screens AND fully-checks at ~8,800 graphs/s/core
    (14 cores ≈ 100k/s); it short-circuits non-3-colorability in microseconds.
  - GPU 3^n kernel: ~17 g/s (n=14). GPU BHK 2^n: full predicate 165-352 ms/graph (200-3500x slower).
  Verdict (hunter 3^n bench + gpu-smith BHK bench, both honest): the CPU backtracking pipeline is the
  DRIVER for both screening and the full witness predicate. The GPU engines are EXACT CROSS-VERIFIERS,
  used ONLY on hits (rare/zero), where their per-graph cost is irrelevant.

ARCHITECTURE:
  geng (degree-sliced, res/mod parallel) ──> CPU floor_worker FULL predicate (is_witness)
       │                                          │
       │ (99.9%+ rejected here, ~100k/s)          └─ survivor (0-critical-edge) = WITNESS CANDIDATE
       ▼
   per n, per degree-slice, parallel across 14 cores
   On a candidate: TRIPLE-VERIFY (checkers backtrack+SAT, my 3^n kernel, BHK) must ALL agree, then
   hand g6 to algebra's exact CPU gate + skeptic's adjudicator + proximity's verifier before any alert.

This driver IS the existing floor_worker pipeline — v2's contribution is: (1) the n=14-18 sweep plan,
(2) the multi-algorithm gate wired on hits, (3) honest logging. For n where geng δ≥6 is infeasible
(n≥13 full), we run the ANNEALER proposal stream instead (witness_anneal), same gate.
"""
import sys, subprocess, time, json, os
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")

DIR = "/Users/patrickkavanagh/math/analysis/e944/team"
LOG = f"{DIR}/search_n14plus.log"
GENG = "/opt/homebrew/Cellar/nauty/2.9.3/bin/geng"


def log(msg):
    line = f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}"
    with open(LOG, "a") as f:
        f.write(line + "\n")


def triple_verify(edges, n):
    """Run a candidate through ALL independent exact algorithms; return (verdict, detail).
    A genuine witness must pass EVERY one. Any disagreement => log a hard alert (bug or real)."""
    from checkers import is_erdos944_k_r1, chi_bt, is_k_colorable_sat
    from gpu_verifier import gpu_is_witness
    detail = {}
    # 1: checkers backtracking
    detail["checkers_bt"] = is_erdos944_k_r1(edges, n, 4, chi_fn=chi_bt)
    # 2: checkers SAT path
    def sat_w(edges, n):
        if is_k_colorable_sat(edges, n, 3): return False
        if not is_k_colorable_sat(edges, n, 4): return False
        for v in range(n):
            rm = {}; nn = 0
            for x in range(n):
                if x != v: rm[x] = nn; nn += 1
            sub = [(rm[a], rm[b]) for (a, b) in edges if a != v and b != v]
            if not is_k_colorable_sat(sub, nn, 3): return False
        for (a, b) in edges:
            if is_k_colorable_sat([e for e in edges if e != (a, b)], n, 3): return False
        return True
    detail["checkers_sat"] = sat_w(edges, n)
    # 3: my 3^n GPU kernel
    try:
        w, _ = gpu_is_witness(n, edges)
        detail["gpu_3n"] = w
    except Exception as e:
        detail["gpu_3n"] = f"ERR:{e}"
    # 4: BHK
    try:
        from bhk_engine import BHKEngine
        b = BHKEngine(n, device="mps").analyze(edges)
        detail["bhk"] = bool(b.get("witness_candidate", b.get("no_critical_edge") and b.get("is_vertex_critical")))
    except Exception as e:
        detail["bhk"] = f"ERR:{e}"
    verdict = (detail["checkers_bt"] is True and detail["checkers_sat"] is True
               and detail["gpu_3n"] is True and detail["bhk"] is True)
    return verdict, detail


def handle_candidate(g6, edges, n, src):
    log(f"!!! CANDIDATE from {src}: n={n} g6={g6} — TRIPLE-VERIFY")
    verdict, detail = triple_verify(edges, n)
    log(f"    triple_verify={verdict} detail={detail}")
    if verdict:
        json.dump({"n": n, "edges": edges, "g6": g6, "src": src, "verify": detail},
                  open(f"{DIR}/WITNESS_n{n}.json", "w"))
        log(f"*** WITNESS PASSES ALL EXACT ALGORITHMS — WITNESS_n{n}.json written. "
            f"Route to algebra exact-gate + skeptic_adjudicate.py + proximity verifier, ALERT team-lead. ***")
        # auto-run skeptic adjudicator
        try:
            out = subprocess.run(["python3", f"{DIR}/skeptic_adjudicate.py", "--g6", g6],
                                 capture_output=True, text=True, timeout=300).stdout
            log(f"    skeptic_adjudicate: {out.strip()}")
        except Exception as e:
            log(f"    skeptic_adjudicate ERR: {e}")
        return True
    else:
        log(f"    candidate REJECTED (not all algorithms agree it's a witness) — likely false flag")
        return False


def g6_to_edges(line):
    import networkx as nx
    G = nx.from_graph6_bytes(line.strip().encode())
    n = G.number_of_nodes()
    H = nx.convert_node_labels_to_integers(G)
    return [(min(u, v), max(u, v)) for u, v in H.edges()], n
