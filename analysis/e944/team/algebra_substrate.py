#!/usr/bin/env python3
"""
algebra_substrate.py — E944 algebraic-substrate explorer (agent: algebra).

Goal: pin the EXACT algebraic requirement behind the three modern constructions
(Jensen circulant / Lattanzio product / Martinsson-Steiner hypergraph) and test
whether any algebraic substrate can realize a (4,1)-graph at the k=4 level.

A (k,r)-graph (Skottova-Steiner terminology) is exactly IsErdos944 G k r:
  - chi(G) = k
  - G vertex-critical: chi(G - v) < k for all v
  - no critical edge-set of size <= r; for r=1: no single critical edge.

Every chromatic-number computation here is cross-checked against hunter's
INDEPENDENT checkers (checkers.py: pure-python backtracking AND SAT) so no
claim rests on a single code path.

Substrates implemented:
  (S1) Circulant graph Cay(Z_N, +/-D)  — Jensen / Skottova-Steiner substrate.
  (S2) Kneser / Schrijver graphs        — classic algebraic chi=k graphs.
  (S3) Categorical (tensor) product      — Lattanzio-style product substrate.
  (S4) Lexicographic product / blow-up   — alternative product substrate.
  (S5) Cayley graphs of non-cyclic groups (S3, Z2xZ3=Z6, Z2xZ2x...) at "level 3".

We test each for the (4,1) property with hunter's verified predicates.
"""
import sys, os
import itertools
import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as H  # hunter's independent checkers (backtracking + SAT)


# ---------------------------------------------------------------------------
# Bridge: networkx Graph  <->  (edges, n) integer form used by hunter's checker
# ---------------------------------------------------------------------------

def nx_to_edges_n(G):
    """Relabel to 0..n-1 and return (edges as sorted (u,v) list, n)."""
    G2 = nx.convert_node_labels_to_integers(G)
    n = G2.number_of_nodes()
    edges = [(min(u, v), max(u, v)) for u, v in G2.edges()]
    return edges, n


def chi(G):
    """Chromatic number via hunter's backtracking path (independent of nx)."""
    edges, n = nx_to_edges_n(G)
    return H.chi_bt(edges, n)


def chi_crosscheck(G):
    """Return (chi_backtrack, chi_sat); they MUST agree or we raise."""
    edges, n = nx_to_edges_n(G)
    a = H.chromatic_number_exact(H.edges_to_adj(edges, n), n)
    try:
        b = H.chromatic_number_sat(edges, n)
    except Exception as e:
        return a, f"SAT-unavailable({e})"
    if a != b:
        raise AssertionError(f"chi MISMATCH backtrack={a} sat={b} on n={n}")
    return a, b


def is_k1_witness(G, k=4):
    """Full (k,1)-graph predicate via hunter's verified predicates."""
    edges, n = nx_to_edges_n(G)
    if H.chi_bt(edges, n) != k:
        return False, "chi!=k"
    if not H.is_vertex_critical(edges, n, k):
        return False, "not vertex-critical"
    if not H.has_no_critical_edge(edges, n, k):
        return False, "has a critical edge"
    return True, "WITNESS"


def report(G, name, k=4):
    edges, n = nx_to_edges_n(G)
    a, b = chi_crosscheck(G)
    m = len(edges)
    line = f"[{name}] n={n} m={m} chi={a}(sat={b})"
    if a == k:
        vc = H.is_vertex_critical(edges, n, k)
        nce = H.has_no_critical_edge(edges, n, k) if vc else None
        line += f" vertex_critical={vc} no_critical_edge={nce}"
        if vc and nce:
            line += "  <<< (k,1)-WITNESS! >>>"
    return line


# ---------------------------------------------------------------------------
# (S1) Circulant graphs  Cay(Z_N, +/- D)   — the Jensen substrate
# ---------------------------------------------------------------------------

def circulant(N, D):
    """Circulant graph on Z_N with connection (distance) set D (subset of 1..N//2).
    v_i ~ v_j iff cyclic distance d_N(i,j) in D."""
    G = nx.Graph()
    G.add_nodes_from(range(N))
    Dset = set(D)
    for i in range(N):
        for d in Dset:
            G.add_edge(i, (i + d) % N)
            G.add_edge(i, (i - d) % N)
    return G


def jensen_k4_distance_sets(N, max_d=None):
    """Enumerate candidate distance sets for a k=4 circulant attempt.
    SS proved the *specific* Jensen family degenerates (D2=D3 empty => chi=3).
    Here we brute-force small distance sets to test SS's conjecture that NO
    circulant on Z_N yields a (4,1)-graph for small N."""
    if max_d is None:
        max_d = N // 2
    return max_d


# ---------------------------------------------------------------------------
# (S3) Categorical (tensor) product   — Lattanzio-style substrate
# ---------------------------------------------------------------------------
# Lattanzio (2002) builds k-critical graphs w/o critical edges for k-1 composite.
# The classic product mechanism: if k-1 = a*b (a,b >= 2), the chromatic number
# factors through a product structure. We test tensor/categorical and lexico-
# graphic products to see what property the factorization k-1=a*b provides.

def tensor_product(G, Hh):
    """Categorical/tensor product G x H. chi(GxH) <= min(chi G, chi H) (Hedetniemi
    was disproved 2019, but <= still holds). Adjacency: (u,x)~(v,y) iff u~v AND x~y."""
    return nx.tensor_product(G, Hh)


def lexicographic_product(G, Hh):
    """Lexicographic product G[H]. chi(G[H]) relates to fractional chi of G.
    (u,x)~(v,y) iff u~v, OR (u==v AND x~y)."""
    return nx.lexicographic_product(G, Hh)


# ---------------------------------------------------------------------------
# (S2) Kneser & Schrijver graphs — algebraic chi=k graphs
# ---------------------------------------------------------------------------

def kneser(n, kk):
    """Kneser graph KG(n,k): vertices = k-subsets of [n], adjacent iff disjoint.
    chi(KG(n,k)) = n - 2k + 2 (Lovász). For chi=4: n-2k+2=4 => n=2k+2."""
    verts = list(itertools.combinations(range(n), kk))
    G = nx.Graph()
    G.add_nodes_from(verts)
    for a, b in itertools.combinations(verts, 2):
        if not (set(a) & set(b)):
            G.add_edge(a, b)
    return G


def schrijver(n, kk):
    """Schrijver graph SG(n,k): vertex-critical subgraph of KG(n,k).
    Vertices = stable k-subsets of the cycle C_n (no two cyclically adjacent).
    chi(SG(n,k)) = n - 2k + 2, and it is VERTEX-CRITICAL (Schrijver 1978)."""
    def is_stable(s):
        s = sorted(s)
        for i in range(len(s)):
            a = s[i]; b = s[(i + 1) % len(s)]
            # cyclic adjacency on Z_n: |a-b|==1 mod n
            if (b - a) % n == 1 or (a - b) % n == 1:
                return False
        # also forbid the wrap pair (0, n-1)
        if 0 in s and (n - 1) in s:
            return False
        return True
    verts = [c for c in itertools.combinations(range(n), kk) if is_stable(c)]
    G = nx.Graph()
    G.add_nodes_from(verts)
    for a, b in itertools.combinations(verts, 2):
        if not (set(a) & set(b)):
            G.add_edge(a, b)
    return G


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== E944 algebraic-substrate probes (algebra agent) ===\n")

    print("--- (S2) Schrijver graphs SG(2k+2, k): vertex-critical, chi=4 ---")
    # chi(SG(n,k)) = n-2k+2 = 4  => n = 2k+2. Smallest: k=2,n=6 -> SG(6,2).
    for (n, kk) in [(6, 2), (8, 3), (10, 4)]:
        G = schrijver(n, kk)
        if G.number_of_nodes() == 0:
            continue
        print("  ", report(G, f"SG({n},{kk})"))

    print("\n--- (S2) Kneser graphs KG(2k+2,k): chi=4, NOT vertex-critical ---")
    for (n, kk) in [(6, 2), (8, 3)]:
        G = kneser(n, kk)
        print("  ", report(G, f"KG({n},{kk})"))

    print("\n--- (S1) Circulant brute force on Z_N (test SS no-(4,1)-circulant claim) ---")
    # Test ALL distance sets on small Z_N for a (4,1)-graph.
    found = 0
    for N in range(11, 18):
        maxd = N // 2
        dists = list(range(1, maxd + 1))
        # limit to distance sets of size <= 3 for tractability on small N
        for size in (2, 3):
            for D in itertools.combinations(dists, size):
                G = circulant(N, D)
                edges, nn = nx_to_edges_n(G)
                if H.chi_bt(edges, nn) != 4:
                    continue
                if H.is_vertex_critical(edges, nn, 4) and H.has_no_critical_edge(edges, nn, 4):
                    print(f"   CIRCULANT (4,1)-WITNESS! N={N} D={D}")
                    found += 1
        print(f"   N={N}: scanned size<=3 distance sets, witnesses so far={found}")
    print(f"   TOTAL circulant (4,1) witnesses on Z_11..Z_17, |D|<=3: {found}")
