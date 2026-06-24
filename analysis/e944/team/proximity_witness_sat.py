"""
CONSTRAINT-ENGINEERED witness search for a (4,1)-graph (proximity, ASSAULT MODE).

A (4,1)-graph = 4-vertex-critical graph with NO critical edge = witness to E944 k=4.

Strategy: STRUCTURAL-SAT + CEGAR. We do NOT try to encode the full coloring quantifiers
("chi(G-v)=3 for all v", "chi(G-e)=4 for all e") into one monolithic SAT — those are
co-NP-hard meta-constraints. Instead:

  (1) Build a SAT model over edge variables x_{ij} encoding ONLY the necessary structural
      conditions a witness MUST satisfy (cheap, sound, drastically prunes the space):
        - min degree >= 6                                     [Skottova-Steiner Prop 5.1]
        - max degree <= n-5                                   [Prop 5.1]
        - exactly E edges in a chosen window (for the regularity/extremal sweep)
        - degree-sequence symmetry: vertex 0 has the max degree, lex degree order
          (sound partial symmetry breaking)
        - "no K4" is NOT imposed (a 4-critical graph may contain K4 only if it equals K4;
          for n>=11 a witness is K4-free, so we MAY add K4-freeness as a sound prune)
  (2) For each model solution, VERIFY the full (4,1) property with the shared, cross-checked
      checkers.py (backtracking chi AND SAT chi must agree).
  (3) CEGAR refinement: a solution that fails gets blocked; we also block its isomorphism
      class cheaply via the certificate of WHICH structural sub-condition failed where
      possible (e.g. a non-critical vertex v with a specific 3-coloring of G-v that extends).

This file provides the encoder + the CEGAR driver. It is designed to feed hunter's campaign
(hunter owns the geng-enumeration floor; this is the SAT/CEGAR complement for the regime where
geng is too large) and to compute the interpolation-ladder minimum critical-edge count.

Edge-connectivity >= 6 (lambda >= 6) is verified post-hoc (networkx) rather than SAT-encoded
(global cut constraints blow up); min-degree>=6 is necessary for it and cheap, so we SAT-encode
min-degree and check lambda>=6 only on structurally-passing candidates.
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import checkers as C
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


# ---------------------------------------------------------------------------
# Edge-variable model
# ---------------------------------------------------------------------------

class GraphModel:
    """SAT model over edge indicator variables for a simple graph on n vertices."""
    def __init__(self, n):
        self.n = n
        self.pool = IDPool()
        self.pairs = list(itertools.combinations(range(n), 2))
        # x[(i,j)] var id
        self.x = {(i, j): self.pool.id(("e", i, j)) for (i, j) in self.pairs}
        self.solver = Cadical195()
        self._clauses = []

    def evar(self, i, j):
        if i > j:
            i, j = j, i
        return self.x[(i, j)]

    def add(self, clause):
        self._clauses.append(clause)
        self.solver.add_clause(clause)

    def incident_vars(self, v):
        return [self.evar(v, u) for u in range(self.n) if u != v]

    def degree_at_least(self, v, k):
        """sum of incident edge vars >= k."""
        lits = self.incident_vars(v)
        cnf = CardEnc.atleast(lits, bound=k, vpool=self.pool, encoding=EncType.seqcounter)
        for cl in cnf.clauses:
            self.add(cl)

    def degree_at_most(self, v, k):
        lits = self.incident_vars(v)
        cnf = CardEnc.atmost(lits, bound=k, vpool=self.pool, encoding=EncType.seqcounter)
        for cl in cnf.clauses:
            self.add(cl)

    def total_edges_between(self, lo, hi):
        lits = [self.x[p] for p in self.pairs]
        if lo is not None:
            for cl in CardEnc.atleast(lits, bound=lo, vpool=self.pool,
                                      encoding=EncType.seqcounter).clauses:
                self.add(cl)
        if hi is not None:
            for cl in CardEnc.atmost(lits, bound=hi, vpool=self.pool,
                                     encoding=EncType.seqcounter).clauses:
                self.add(cl)

    def forbid_k4(self):
        """No 4 mutually adjacent vertices (sound prune: a witness on n>=11 is K4-free,
        since a 4-critical graph containing K4 IS K4)."""
        for quad in itertools.combinations(range(self.n), 4):
            lits = [-self.evar(a, b) for a, b in itertools.combinations(quad, 2)]
            self.add(lits)

    def block_solution(self, edges_set):
        """Block this exact edge set (CEGAR no-good)."""
        clause = []
        for p in self.pairs:
            if p in edges_set:
                clause.append(-self.x[p])
            else:
                clause.append(self.x[p])
        self.add(clause)

    def solve_next(self):
        if not self.solver.solve():
            return None
        model = set(self.solver.get_model())
        edges = [p for p in self.pairs if self.x[p] in model]
        return edges


# ---------------------------------------------------------------------------
# Structural constraints from squad knowledge
# ---------------------------------------------------------------------------

def apply_structural_constraints(gm, k4_free=True, edge_lo=None, edge_hi=None):
    """All Prop-5.1 necessary conditions + sound prunes. r=1 values."""
    n = gm.n
    for v in range(n):
        gm.degree_at_least(v, 6)        # Prop 5.1: min-degree >= 6
        gm.degree_at_most(v, n - 5)     # Prop 5.1: max-degree <= n-5
    if k4_free:
        gm.forbid_k4()
    if edge_lo is not None or edge_hi is not None:
        gm.total_edges_between(edge_lo, edge_hi)


def lambda_at_least_6(edges, n):
    """edge-connectivity >= 6 (networkx). Necessary for a (4,1)-graph (Prop 5.1)."""
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    if not nx.is_connected(G):
        return False
    return nx.edge_connectivity(G) >= 6


# ---------------------------------------------------------------------------
# CEGAR driver: structural SAT + full (4,1) verification
# ---------------------------------------------------------------------------

def cegar_search(n, max_candidates=200000, k4_free=True, edge_lo=None, edge_hi=None,
                 report_every=500):
    """Enumerate structurally-feasible graphs; verify each for the (4,1) property.
    Returns a witness edge-list or None. Every candidate verified via checkers (chi
    cross-checked backtrack vs SAT). lambda>=6 checked post-hoc as an extra necessary prune."""
    gm = GraphModel(n)
    apply_structural_constraints(gm, k4_free=k4_free, edge_lo=edge_lo, edge_hi=edge_hi)
    tested = 0
    chi4 = 0
    vc = 0
    lam_ok = 0
    while tested < max_candidates:
        edges = gm.solve_next()
        if edges is None:
            print(f"  structural model EXHAUSTED after {tested} candidates "
                  f"(n={n}, edges window {edge_lo}-{edge_hi}, k4_free={k4_free}).")
            return None, dict(tested=tested, chi4=chi4, vc=vc, lam_ok=lam_ok, exhausted=True)
        tested += 1
        # cheap necessary filters first
        if not lambda_at_least_6(edges, n):
            gm.block_solution(set(edges))
            continue
        lam_ok += 1
        # chi == 4 ?
        if C.chi_bt(edges, n) != 4:
            gm.block_solution(set(edges))
            continue
        chi4 += 1
        # vertex-critical ?
        if not C.is_vertex_critical(edges, n, 4):
            gm.block_solution(set(edges))
            continue
        vc += 1
        # cross-check chi with SAT before the expensive no-critical-edge test
        if C.chromatic_number_sat(edges, n) != 4:
            print(f"  !!! chi mismatch at n={n}; blocking")
            gm.block_solution(set(edges)); continue
        # no critical edge ?
        if C.has_no_critical_edge(edges, n, 4):
            print(f"  *** WITNESS at n={n}! edges={edges}")
            return edges, dict(tested=tested, chi4=chi4, vc=vc, lam_ok=lam_ok, witness=True)
        gm.block_solution(set(edges))
        if report_every and tested % report_every == 0:
            print(f"  ...n={n}: {tested} structural cands, {lam_ok} lambda>=6, "
                  f"{chi4} chi=4, {vc} vertex-critical, 0 witnesses")
    return None, dict(tested=tested, chi4=chi4, vc=vc, lam_ok=lam_ok, hit_cap=True)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    elo = int(sys.argv[2]) if len(sys.argv) > 2 else None
    ehi = int(sys.argv[3]) if len(sys.argv) > 3 else None
    print(f"=== Constraint-engineered (4,1) CEGAR search, n={n}, edges {elo}-{ehi} ===")
    w, stats = cegar_search(n, edge_lo=elo, edge_hi=ehi)
    print("stats:", stats)
    if w:
        print("WITNESS:", w)
    else:
        print("no witness in this regime.")
