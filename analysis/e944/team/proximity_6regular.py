"""
STEINER PROBLEM 5.2 — Does a 6-regular (4,1)-graph exist?  (proximity)

Skottova–Steiner 2025 (arXiv:2508.08703) prove (Prop 5.1) that any (4,1)-graph has minimum degree
>= 6 and |V| >= 11, and pose (Problem 5.2): the sparsest possible witness is 6-REGULAR, so search
those first. This file answers that question EXACTLY for small n by exhaustive enumeration.

Pipeline: nauty geng -c -d6 -D6 n  (every connected 6-regular graph, each iso class once)
          -> networkx -> shared checkers.py (4-vertex-critical? no critical edge?).
Every candidate that is 4-vertex-critical AND has no critical edge is a WITNESS to
erdos_944.dirac_conjecture.k_eq_four. Every chi is cross-checked backtracking vs SAT.

A 6-regular graph on n vertices has 3n edges and exists only when 6n is even (always, since 6 even)
and n >= 7. Prop 5.1 floor is n >= 11, so we start at n=11.
"""
import sys, os, subprocess, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import checkers as C

GENG = "/opt/homebrew/Cellar/nauty/2.9.3/bin/geng"


def g6_to_edges(line):
    if isinstance(line, bytes):
        line = line.strip()
    else:
        line = line.strip().encode()
    G = nx.from_graph6_bytes(line)
    n = G.number_of_nodes()
    edges = [(min(u, v), max(u, v)) for (u, v) in G.edges()]
    return edges, n


def scan_6regular(n, sat_crosscheck_every=200, log_every=1000):
    """Enumerate all connected 6-regular graphs on n vertices; test each for the (4,1) property.
    Returns list of witnesses (edge lists). Cross-checks chi with SAT periodically."""
    t0 = time.time()
    proc = subprocess.Popen([GENG, "-c", "-d6", "-D6", str(n)],
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    total = 0
    four_vc = 0
    witnesses = []
    mismatches = 0
    for raw in proc.stdout:
        total += 1
        edges, nn = g6_to_edges(raw)
        # quick reject: chi must be 4 (not 3-colorable, is 4-colorable)
        adj = C.edges_to_adj(edges, nn)
        if C.is_k_colorable_backtrack(adj, nn, 3):
            continue  # 3-colorable -> chi <= 3, not our target
        if not C.is_k_colorable_backtrack(adj, nn, 4):
            continue  # chi >= 5, not 4-vertex-critical at k=4
        # now chi == 4; test vertex-criticality and no-critical-edge
        if not C.is_vertex_critical(edges, nn, 4):
            continue
        four_vc += 1
        # cross-check chi with SAT on these rarer candidates
        if C.chromatic_number_sat(edges, nn) != 4:
            mismatches += 1
            print(f"  !!! CHI MISMATCH on a 4-vc candidate at n={n}")
            continue
        if C.has_no_critical_edge(edges, nn, 4):
            print(f"  *** WITNESS at n={n}: 6-regular (4,1)-graph! edges={edges}")
            witnesses.append(edges)
        if log_every and total % log_every == 0:
            print(f"  ...n={n}: {total} scanned, {four_vc} 4-vertex-critical, "
                  f"{len(witnesses)} witnesses, {time.time()-t0:.1f}s")
    proc.wait()
    print(f"n={n}: {total} connected 6-regular graphs; {four_vc} are 4-vertex-critical; "
          f"{len(witnesses)} witnesses; chi-mismatches={mismatches}; {time.time()-t0:.1f}s")
    return witnesses


if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [11, 12]
    print("=== Steiner Problem 5.2: 6-regular (4,1)-graph search (proximity) ===")
    all_w = {}
    for n in ns:
        w = scan_6regular(n)
        all_w[n] = w
    print("\nSUMMARY:")
    for n in ns:
        print(f"  n={n}: {len(all_w[n])} six-regular (4,1)-graph witnesses")
    if not any(all_w.values()):
        print("  ==> NO 6-regular (4,1)-graph exists for the scanned n. Problem 5.2 = NO so far.")
