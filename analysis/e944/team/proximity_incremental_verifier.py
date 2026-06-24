"""
Incremental (4,1)-witness VERIFIER — ENC-2 + ENC-6 combined (proximity, invention blitz).

Replaces the CEGAR no-critical-edge loop AND the n baked colorings with ONE persistent SAT solver
using activation-literal-guarded clauses. Both co-NP witness halves become incremental assumption
solves that share learned clauses:

  - VERTEX-criticality (ENC-2): per-vertex activation literal av(u); "G-v 3-colorable?" = solve under
    {av(u):u!=v} + {not av(v)}. Vertex-critical (lower half) <=> all SAT.
  - NO-CRITICAL-EDGE (ENC-6): per-edge activation literal ae(i); "G-e_i 3-colorable?" = solve under
    {ae(j):j!=i} + {not ae(i)}. No critical edge <=> all UNSAT.
  - chi(G) = 4: chi<=4 via a 4-colorability check; chi>=4 via "G not 3-colorable" (the full-graph
    assumption with everything active). vertex-critical + chi=4 needs chi(G)=4 exactly.

ROLE (settled with hunter, 2026-06-10): this is the INDEPENDENT THIRD VERIFICATION PATH in the
candidate-witness adjudication chain — a DIFFERENT solver (Cadical SAT) + DIFFERENT encoding
(activation-literal deletion) than checkers.py backtracking and skeptic_adjudicate's chi_A/chi_B. Its
value is ENCODING DIVERSITY for quadruple-confidence on a SINGLE candidate, NOT enumeration throughput.
SPEED (hunter-benchmarked; accept as correct): this verifier is SLOWER than hunter's optimized bitmask
floor_worker for fresh-graph scanning — 0.36ms vs 0.19ms at n=16, 0.45 vs 0.31 at n=18. SAT instance
setup/teardown dominates per-graph; the incremental advantage only helps WITHIN one graph's n+m checks,
which cheap backtracking already handles at this size. (My earlier "~2x faster" was vs the heavier
networkx-based checkers.py, NOT floor_worker — a wrong-baseline comparison; corrected.) So: use this
ONLY to ADJUDICATE a candidate (independent code path, speed irrelevant on one graph), NOT for bulk
scanning — for scanning use floor_worker. Cross-checked vs checkers.py + hunter's floor_worker (agrees
on C13(1,2,5) + a 2000-graph |E|=40 batch, hunter-verified, all verdicts match).

NOTE on a subtlety: vertex-criticality requires chi(G)=4 AND chi(G-v)<=3 for all v. The activation
trick models G-v (and G-e) by relaxing the guarded clauses. We verify chi(G)=4 separately (not
3-colorable as full graph, but 4-colorable).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.formula import IDPool
import checkers as C


class IncrementalWitnessVerifier:
    """One persistent solver; vertex- and edge-deactivation via assumptions."""
    def __init__(self, edges, n):
        self.edges = list(edges)
        self.n = n
        self.pool = IDPool()
        self.x = lambda u, c: self.pool.id(("x", u, c))
        self.av = lambda u: self.pool.id(("av", u))
        self.ae = lambda i: self.pool.id(("ae", i))
        self.s3 = Cadical195()   # 3-coloring solver with both vertex+edge activation guards
        self._build_3col()

    def _build_3col(self):
        s, n, edges = self.s3, self.n, self.edges
        for u in range(n):
            s.add_clause([self.x(u, c) for c in range(3)])
            for c1, c2 in combinations(range(3), 2):
                s.add_clause([-self.x(u, c1), -self.x(u, c2)])
        for i, (u, v) in enumerate(edges):
            # edge i proper only if both endpoints active AND edge active
            for c in range(3):
                s.add_clause([-self.av(u), -self.av(v), -self.ae(i), -self.x(u, c), -self.x(v, c)])

    def _all_active_except_vertex(self, v):
        return ([self.av(u) for u in range(self.n) if u != v] + [-self.av(v)]
                + [self.ae(i) for i in range(len(self.edges))])

    def _all_active_except_edge(self, i):
        return ([self.av(u) for u in range(self.n)]
                + [self.ae(j) for j in range(len(self.edges)) if j != i] + [-self.ae(i)])

    def _all_active(self):
        return [self.av(u) for u in range(self.n)] + [self.ae(i) for i in range(len(self.edges))]

    def is_3colorable_full(self):
        return self.s3.solve(assumptions=self._all_active())

    def vertex_critical_lower(self):
        """True iff G-v is 3-colorable for every v (the vertex-criticality lower half)."""
        for v in range(self.n):
            if not self.s3.solve(assumptions=self._all_active_except_vertex(v)):
                return False
        return True

    def no_critical_edge(self):
        """True iff G-e is NOT 3-colorable for every edge e."""
        for i in range(len(self.edges)):
            if self.s3.solve(assumptions=self._all_active_except_edge(i)):
                return False, self.edges[i]
        return True, None

    def chi_is_4(self):
        """chi(G)=4: not 3-colorable (full) AND 4-colorable."""
        if self.is_3colorable_full():
            return False
        return C.is_k_colorable_backtrack(C.edges_to_adj(self.edges, self.n), self.n, 4)

    def is_witness(self):
        """Full (4,1) check: chi=4, vertex-critical, no critical edge."""
        if not self.chi_is_4():
            return False
        if not self.vertex_critical_lower():
            return False
        nce, _ = self.no_critical_edge()
        return nce

    def close(self):
        self.s3.delete()


def verify(edges, n):
    v = IncrementalWitnessVerifier(edges, n)
    r = v.is_witness()
    v.close()
    return r


if __name__ == "__main__":
    # Self-test against checkers on circulant near-misses + a known non-witness.
    def circ(n, S):
        e = set()
        for i in range(n):
            for d in S:
                j = (i + d) % n
                e.add((min(i, j), max(i, j)))
        return sorted(e)
    cases = [(13, (1, 2, 5)), (14, (1, 2, 5)), (16, (1, 2, 5)), (13, (1, 3, 5))]
    print("graph | incremental is_witness | checkers is_erdos944 | AGREE")
    allok = True
    for n, S in cases:
        g = circ(n, S)
        inc = verify(g, n)
        ref = C.is_erdos944_k_r1(g, n, 4)
        ok = (inc == ref)
        allok &= ok
        print(f"C{n}{S} | {inc} | {ref} | {ok}")
    print("ALL AGREE" if allok else "MISMATCH — DO NOT USE")
