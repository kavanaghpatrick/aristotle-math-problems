"""
Decisive test of the "vertex-transitive repair" route:
Search ALL circulants C_N(S) for a k=4 Dirac witness.

Rationale: Jensen's witness IS a circulant. count's C_7(1,2) shows circulants can
get HALF their edges non-critical at k=4. If a k=4 witness exists in circulant
(=vertex-transitive abelian) form, criticality is constant on each connection-set
orbit, so we only need: chi=4, vertex-critical, and EVERY connection difference
gives a non-critical edge.

For a circulant C_N(S) (S subset of {1..N/2}), the edge orbits correspond to the
distances in S. Vertex-transitivity => an edge of distance d is critical iff ALL
distance-d edges are. So "no critical edge" <=> for every d in S, deleting one
distance-d edge keeps chi=4.

We brute-force N up to a bound, all connection sets S (up to the obvious
symmetry), filter to chi=4 vertex-critical, and check criticality per distance.
This is an EXISTENCE search over the vertex-transitive abelian family — a negative
result over a range is a real (range-bounded) statement; a positive result is a
WITNESS.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical


def circulant(N, S):
    G = nx.Graph()
    G.add_nodes_from(range(N))
    for i in range(N):
        for d in S:
            G.add_edge(i, (i + d) % N)
    return G


def edge_distance(N, u, v):
    d = abs(u - v) % N
    return min(d, N - d)


def no_critical_edge_circulant(G, N, S, chi):
    """For a circulant, check one representative edge per distance d in S."""
    for d in S:
        H = G.copy()
        H.remove_edge(0, d % N)  # representative distance-d edge
        if chromatic_number(H) >= chi:
            continue  # this distance's edges are non-critical
        else:
            return False  # this distance is critical
    return True


def search(N_min, N_max, max_S=4):
    found = []
    for N in range(N_min, N_max + 1):
        half = N // 2
        diffs = list(range(1, half + 1))
        # connection sets of size 2..max_S (size>=2 to have a chance at chi>=3;
        # need chi=4 so typically >=2 distances)
        for size in range(2, max_S + 1):
            for S in itertools.combinations(diffs, size):
                G = circulant(N, list(S))
                # quick chi filter
                if not nx.is_connected(G):
                    continue
                chi = chromatic_number(G)
                if chi != 4:
                    continue
                if not is_vertex_critical(G, 4):
                    continue
                if no_critical_edge_circulant(G, N, list(S), 4):
                    found.append((N, S))
                    print(f"  *** WITNESS CANDIDATE: C_{N}({list(S)}) chi=4 "
                          f"vertex-critical, NO critical edge ***")
        if N % 5 == 0 or N == N_max:
            print(f"  ...searched through N={N}, witnesses so far: {len(found)}")
    return found


if __name__ == "__main__":
    print("=== Circulant k=4 witness search (vertex-transitive abelian family) ===")
    # Keep runtime bounded: small connection sets, modest N.
    found = search(5, 26, max_S=4)
    print()
    if found:
        print("WITNESS CANDIDATES (verify independently!):", found)
    else:
        print("NO circulant k=4 Dirac witness with |S|<=4 for N in [5,26].")
        print("(Range-bounded negative result. Larger N / |S| not excluded.)")
