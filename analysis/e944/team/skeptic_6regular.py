#!/usr/bin/env python3
"""
skeptic_6regular.py — Steiner's Problem 5.2 at the floor: exhaustively test all
connected 6-REGULAR graphs on n vertices for the (4,1)-property (4-vertex-critical
with no critical edge). 6-regular is the SPARSEST graph allowed by Skottova–Steiner
Prop 5.1 (min-deg >= 6); it is the literature-sanctioned first target (their Problem 5.2).

Two independent chi-checkers (backtrack chi_A + SAT chi_B) must agree on every
decision; a mismatch ABORTS (no buggy-checker false witness).

Usage: python3 skeptic_6regular.py <n>
"""
import subprocess, sys
import networkx as nx
from skeptic_enum import nx_to_adj, chi_A, chi_B, edges_of, delete_vertex, delete_edge

GENG = "/opt/homebrew/bin/geng"

def gen_6regular(n):
    p = subprocess.Popen([GENG, "-c", "-d6", "-D6", str(n)],
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in p.stdout:
        line = line.strip()
        if line:
            yield nx.from_graph6_bytes(line)
    p.wait()

def run(n):
    examined = vcrit = witnesses = 0
    for G in gen_6regular(n):
        examined += 1
        adj, nn = nx_to_adj(G)
        if chi_A(adj, nn) != 4:
            continue
        if not all(chi_A(*delete_vertex(adj, nn, v)) < 4 for v in range(nn)):
            continue
        if chi_B(adj, nn) != 4:
            raise SystemExit(f"CHECKER DISAGREE chi on {nx.to_graph6_bytes(G,header=False)}")
        vcrit += 1
        has_crit = False
        for e in edges_of(adj, nn):
            a2, n2 = delete_edge(adj, nn, e)
            if chi_A(a2, n2) < 4:
                if chi_B(a2, n2) >= 4:
                    raise SystemExit(f"CHECKER DISAGREE edge {e} on {nx.to_graph6_bytes(G,header=False)}")
                has_crit = True
                break
        if not has_crit:
            witnesses += 1
            print(f"  !!! WITNESS: 6-regular (4,1)-graph n={n}: "
                  f"{nx.to_graph6_bytes(G, header=False).strip().decode()}")
    print(f"n={n} 6-regular: examined={examined}  4-vertex-critical={vcrit}  WITNESSES={witnesses}")
    print(f"# RESULT n={n}: {'NO 6-regular (4,1)-graph' if witnesses==0 else 'WITNESS FOUND'}.")
    return witnesses

if __name__ == "__main__":
    n = int(sys.argv[1])
    sys.exit(0 if run(n) == 0 else 1)
