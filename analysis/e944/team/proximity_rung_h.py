"""
RUNG H — the Martinsson-Steiner hypergraph route to a (4,1)-graph (proximity).

M-S 2023 (arXiv:2310.12891) build a (k,r)-graph as G := complement of the 2-section of an
s-uniform hypergraph H on n = s(k-1)+1 vertices satisfying:
  (i)  for every vertex v, H - v has a PERFECT MATCHING (partition of the other n-1 vertices
       into (n-1)/s = k-1 disjoint hyperedges);
  (ii) LOCAL SPARSITY (Lemma-3 form): for every F subset E(H) with |F| <= 2^{s+1}=32,
       |union of F| >= (s-1)|F|.
Their Lemma 5 then gives, for X of size s+1, |E(2-section[X])| <= C(s,2)+2, which forces
alpha(G - R) <= s for |R| <= r, hence chi(G - R) >= n/s > k-1: G is a (k,r)-graph.

For r=1: s = r+3 = 4, k=4, n = 4*3+1 = 13.

RIGID-n FACT: G-v is 3-colorable because H-v's perfect matching splits the other 12 vertices
into (n-1)/s = (n-1)/4 independent sets, and for chi(G-v) <= k-1 = 3 we need (n-1)/4 = 3, i.e.
n = 13. s = 4 is fixed by r=1. So the (4,1) instance of this route lives ENTIRELY on n=13,
s=4 hypergraphs -- there is NO other n to try.

TWO RESULTS in this file:

(A) The M-S SUFFICIENT CONDITION is INFEASIBLE at n=13 (proved by a counting argument, verified
    here):
      * property (i) forces |E(H)| >= ceil(13*3 / 9) = 5 hyperedges
        (each of 13 vertices needs 3 matching-hyperedges; each hyperedge serves at most
         13-4 = 9 vertices' matchings);
      * but the Lemma-3 form of property (ii) FAILS for any 5 hyperedges: |F|=5 demands
        |union| >= 3*5 = 15 > 13 = n.
    Hence NO 4-uniform hypergraph on 13 vertices satisfies BOTH (i) and the Lemma-3 (ii).
    ==> The M-S route, via its own sufficient condition, cannot produce a (4,1)-graph. This is
        a SHARP, LOCALIZED death of the probabilistic route at the minimal (only) n for k=4.

(B) HONEST stronger test: the Lemma-3 (ii) is only SUFFICIENT, not necessary. The graph G might
    still be a (4,1)-graph even if (ii) fails, as long as alpha(G - e) <= 4 holds directly. So we
    ALSO search property-(i) hypergraphs on n=13 directly, build G = complement-of-2-section, and
    test it against the squad's shared checkers.py (cross-checked backtrack + SAT chi). If ANY G
    is a (4,1)-graph, we have a witness; if the property-(i) hypergraphs all yield G that fail,
    that documents the route is empty on the graph side too (for the sampled / enumerated family).

All chi computations go through checkers.py (two independent code paths must agree).
"""
import sys, os, random, math
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as C

S = 4
K = 4
N = S * (K - 1) + 1   # = 13


# ---------------------------------------------------------------------------
# (A) The counting infeasibility of the M-S sufficient condition
# ---------------------------------------------------------------------------

def report_sufficient_condition_infeasible():
    min_edges = math.ceil(N * (K - 1) / (N - S))   # ceil(13*3 / 9)
    print("(A) M-S SUFFICIENT CONDITION at n=13, s=4:")
    print(f"    property (i) forces |E(H)| >= ceil({N}*{K-1} / {N-S}) = {min_edges}")
    f_break = None
    for f in range(1, N + 1):
        if (S - 1) * f > N:
            f_break = f
            break
    print(f"    property (ii) [Lemma-3 form] FAILS at |F| = {f_break}: "
          f"need union >= {(S-1)*f_break} > {N} = n")
    feasible = min_edges < f_break
    print(f"    min edges = {min_edges}, first infeasible |F| = {f_break} "
          f"==> any valid H has |F|={min_edges} >= {f_break} hyperedges that violate (ii)."
          if not feasible else "    (feasible window exists)")
    print(f"    VERDICT: M-S sufficient condition is {'INFEASIBLE' if not feasible else 'feasible'} "
          f"at the unique n={N} for (k=4,r=1).\n")
    return not feasible


# ---------------------------------------------------------------------------
# Property (i) checker (exact)
# ---------------------------------------------------------------------------

def has_perfect_matching_after_delete(hyperedges, v):
    verts = frozenset(u for u in range(N) if u != v)
    cand = [frozenset(e) for e in hyperedges if v not in e]

    def bt(remaining):
        if not remaining:
            return True
        u = min(remaining)
        for e in cand:
            if u in e and e <= remaining:
                if bt(remaining - e):
                    return True
        return False
    return bt(verts)


def property_i(hyperedges):
    return all(has_perfect_matching_after_delete(hyperedges, v) for v in range(N))


# ---------------------------------------------------------------------------
# G := complement of the 2-section of H  (the M-S graph)
# ---------------------------------------------------------------------------

def two_section(hyperedges):
    sec = set()
    for e in hyperedges:
        for a, b in combinations(sorted(e), 2):
            sec.add((a, b))
    return sec


def complement_of_two_section(hyperedges):
    sec = two_section(hyperedges)
    return [(a, b) for a, b in combinations(range(N), 2) if (a, b) not in sec]


def verify_is_41_graph(hyperedges, verbose=False):
    """Build G and check it is a (4,1)-graph using the shared, cross-checked checkers."""
    G = complement_of_two_section(hyperedges)
    chi_bt = C.chi_bt(G, N)
    if chi_bt != K:
        return False, f"chi={chi_bt}!=4"
    chi_sat = C.chromatic_number_sat(G, N)
    if chi_bt != chi_sat:
        return False, f"CHI MISMATCH bt={chi_bt} sat={chi_sat}"
    if not C.is_vertex_critical(G, N, K):
        return False, "not vertex-critical"
    if not C.has_no_critical_edge(G, N, K):
        return False, "has a critical edge"
    return True, "(4,1)-GRAPH"


# ---------------------------------------------------------------------------
# (B) Direct search over property-(i) hypergraphs -> test the graph directly
# ---------------------------------------------------------------------------

def random_property_i_hypergraph(rng):
    """Assemble H by laying down, for each vertex v, one random perfect matching of the other 12
    vertices. This GUARANTEES property (i). Returns the set of distinct hyperedges."""
    edges = set()
    for v in range(N):
        others = [u for u in range(N) if u != v]
        rng.shuffle(others)
        for i in range(0, 12, 4):
            edges.add(frozenset(others[i:i + 4]))
    return [set(e) for e in edges]


def search_graph_side(trials=4000, seed=0, report_every=1000):
    """For many property-(i) hypergraphs, build G and test if it is a (4,1)-graph.
    Records the distribution of chi(G) and how G fails, to document the route on the graph side."""
    rng = random.Random(seed)
    from collections import Counter
    chi_hist = Counter()
    fail_hist = Counter()
    edge_count_hist = Counter()
    found = None
    for t in range(trials):
        H = random_property_i_hypergraph(rng)
        edge_count_hist[len(H)] += 1
        G = complement_of_two_section(H)
        chi = C.chi_bt(G, N)
        chi_hist[chi] += 1
        if chi == K:
            ok, why = verify_is_41_graph(H)
            if ok:
                print(f"[trial {t}] *** (4,1)-GRAPH WITNESS via M-S route! |E(H)|={len(H)} ***")
                found = H
                break
            fail_hist[why] += 1
        else:
            fail_hist[f"chi={chi}"] += 1
        if report_every and t % report_every == 0 and t > 0:
            print(f"  ...{t} trials; chi(G) dist so far: {dict(chi_hist)}")
    print(f"\n(B) Direct graph-side search over {trials} property-(i) hypergraphs on n={N}:")
    print(f"    |E(H)| distribution: {dict(sorted(edge_count_hist.items()))}")
    print(f"    chi(G) distribution: {dict(sorted(chi_hist.items()))}")
    print(f"    failure reasons:     {dict(fail_hist)}")
    if found is None:
        print("    NO (4,1)-graph found via this route in the sampled family.")
    return found


if __name__ == "__main__":
    print(f"=== RUNG H: Martinsson-Steiner hypergraph route, s={S}, k={K}, n={N} ===\n")
    report_sufficient_condition_infeasible()
    search_graph_side(trials=3000, seed=0, report_every=1000)
