#!/usr/bin/env python3
"""
skeptic_adjudicate.py — VERIFICATION COMMAND: instant dual-checker adjudication of a
claimed E944 (4,1)-witness. No graph is called a witness without passing this.

A candidate PASSES as a genuine (4,1)-witness iff, with BOTH independent χ-checkers
(chi_A backtracking + chi_B SAT) agreeing on EVERY decision:
  (A) χ(G) == 4
  (B) vertex-critical: χ(G − v) < 4 for every vertex v
  (C) NO critical edge: χ(G − e) == 4 for every edge e
A disagreement between checkers is a HARD FAIL (we do not trust a single checker).

Usage:
  python3 skeptic_adjudicate.py --g6 'ICpdbY{]_'            # graph6 string
  python3 skeptic_adjudicate.py --g6file candidates.g6      # one g6 per line
  python3 skeptic_adjudicate.py --edges '0-1,0-2,...' --n 13 # explicit edge list

Exit 0 = at least one genuine witness found (ALERT). Exit 1 = none verified.
"""
import sys, argparse
import networkx as nx
from skeptic_enum import nx_to_adj, chi_A, chi_B, edges_of, delete_vertex, delete_edge


def chi_both(adj, n, ctx=""):
    a = chi_A(adj, n); b = chi_B(adj, n)
    if a != b:
        raise SystemExit(f"HARD FAIL — χ-checkers DISAGREE (A={a},B={b}) {ctx}. "
                         "A buggy checker invalidates the verdict; do NOT celebrate.")
    return a


def adjudicate(G, label=""):
    adj, n = nx_to_adj(G)
    rep = {"label": label, "n": n, "m": len(edges_of(adj, n))}
    # (A) χ == 4
    c = chi_both(adj, n, f"[{label}] χ(G)")
    rep["chi"] = c
    if c != 4:
        rep["verdict"] = f"NOT A WITNESS — χ(G)={c} ≠ 4"
        return rep, False
    # (B) vertex-critical
    bad_v = []
    for v in range(n):
        cv = chi_both(*delete_vertex(adj, n, v), ctx=f"[{label}] χ(G−v{v})")
        if cv >= 4:
            bad_v.append(v)
    if bad_v:
        rep["verdict"] = f"NOT A WITNESS — not vertex-critical; χ(G−v)≥4 at vertices {bad_v[:10]}"
        return rep, False
    rep["vertex_critical"] = True
    # (C) no critical edge
    crit = []
    for e in edges_of(adj, n):
        ce = chi_both(*delete_edge(adj, n, e), ctx=f"[{label}] χ(G−e{e})")
        if ce < 4:
            crit.append(e)
    rep["num_critical_edges"] = len(crit)
    if crit:
        rep["verdict"] = (f"NOT A WITNESS — has {len(crit)} critical edge(s); "
                          f"e.g. {crit[:5]}. (best approximate witness, not a true one)")
        return rep, False
    rep["verdict"] = "*** GENUINE (4,1)-WITNESS *** — χ=4, vertex-critical, ZERO critical edges. DUAL-CHECKER CONFIRMED."
    rep["g6"] = nx.to_graph6_bytes(G, header=False).strip().decode()
    return rep, True


def parse_edges(s, n):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for tok in s.split(","):
        tok = tok.strip()
        if not tok:
            continue
        a, b = tok.split("-")
        G.add_edge(int(a), int(b))
    return G


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--g6")
    ap.add_argument("--g6file")
    ap.add_argument("--edges")
    ap.add_argument("--n", type=int)
    args = ap.parse_args()

    cands = []
    if args.g6:
        cands.append((args.g6, nx.from_graph6_bytes(args.g6.encode())))
    if args.g6file:
        with open(args.g6file) as f:
            for i, line in enumerate(f):
                line = line.strip()
                if line:
                    cands.append((f"{args.g6file}:{i}", nx.from_graph6_bytes(line.encode())))
    if args.edges:
        if not args.n:
            raise SystemExit("--edges requires --n")
        cands.append(("edges", parse_edges(args.edges, args.n)))
    if not cands:
        raise SystemExit("provide --g6, --g6file, or --edges/--n")

    any_witness = False
    for label, G in cands:
        rep, ok = adjudicate(G, label)
        any_witness = any_witness or ok
        print(f"[{rep['label']}] n={rep['n']} m={rep['m']} χ={rep.get('chi','?')} "
              f"critEdges={rep.get('num_critical_edges','?')} -> {rep['verdict']}")
        if ok:
            print(f"    g6 = {rep['g6']}")
    sys.exit(0 if any_witness else 1)


if __name__ == "__main__":
    main()
