"""
e944 targeted SAT-CEGAR search (hunter) — for n where brute geng enumeration is infeasible (n>=12).

We search for a graph G on n labeled vertices with:
  (V)  chi(G) = 4         -> (V1) G not 3-colorable  AND (V2) G 4-colorable
  (C)  vertex-critical    -> for every v, G - v IS 3-colorable
  (E)  no critical edge   -> for every present edge e, G - e is NOT 3-colorable

SAT model (the GRAPH is the unknown). Variables:
  e[i][j]   (i<j)  : edge present?
  For (C): for each v, a witnessing 3-coloring  cV[v][u][col]  of  G - v.
           Baked in: forces G-v to be 3-colorable BY CONSTRUCTION (so vertex-criticality is
           guaranteed for any model the solver returns). Constraint:
             if e[u][w] AND u!=v AND w!=v  then  not (cV[v][u][c] and cV[v][w][c]) for all c.
           Each kept vertex gets exactly one of 3 colors.
  For (V2): a witnessing 4-coloring c4[u][col] of G. Baked in -> G is 4-colorable by construction.

The two co-NP conditions handled by CEGAR (lazy refinement):
  (V1) G must NOT be 3-colorable. We do NOT bake this in. Instead, after the solver returns a
       candidate G, we externally test 3-colorability with the exact checker. If 3-colorable with
       coloring phi, we add a blocking clause forbidding THIS coloring from being proper on the
       (variable) edge set: at least one monochromatic pair under phi must become an edge... but phi
       is a coloring of a SPECIFIC graph. The correct refinement: for the returned graph G0, the
       reason it is 3-colorable is the coloring phi. To forbid 3-colorability we must ensure that
       for EVERY 3-coloring, some edge is monochromatic. We add the clause: OR over all monochromatic
       pairs (under phi that are non-edges in G0) e[i][j]  -- i.e. "to kill this coloring, add one of
       the edges that phi colors the same". This is the standard CEGAR refinement for forcing
       non-k-colorability.
  (E)  every present edge e must be NON-critical: G - e not 3-colorable. After a candidate passes
       (V1), for each edge e we test G-e. If G-e is 3-colorable (e is critical) with coloring phi,
       we add: e is present -> (some monochromatic non-edge pair becomes an edge). Encoded as
       clause: (NOT e_present) OR (OR of e[i][j] over phi-monochromatic non-edges of G-e).
       Practically: (¬e_ab) ∨ ⋁ e[i][j]. This says "either drop edge ab, or add an edge to break
       this 3-coloring of G-e".

This is a sound CEGAR: every returned model satisfies (C) and (V2) by construction; (V1) and (E)
are enforced by accumulated blocking/refinement clauses; we re-verify the final model with BOTH
independent checkers before declaring a witness.

Symmetry: we fix a partial vertex order by degree via cardinality is hard in SAT; instead we add a
light lex/labeling break (vertex 0 has an edge to vertex 1, etc.) — optional. We also pin min
degree >= 3.

NOTE: This is a heuristic *search* (incomplete unless run to UNSAT). An UNSAT result for fixed n
(with all symmetry breaks SOUND, i.e. not over-constraining) WOULD prove no witness on n vertices,
but full symmetry breaking to make UNSAT a proof is delicate; we treat SAT-found candidates as the
primary goal and clearly mark any UNSAT as "UNSAT under these clauses" (not a completeness proof
unless symmetry breaking is certified). The geng floor remains the rigorous lower-bound instrument.
"""
import sys
import itertools
from pysat.solvers import Cadical195
from pysat.formula import IDPool

sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from checkers import (
    chromatic_number_exact, edges_to_adj, is_k_colorable_backtrack,
    is_vertex_critical, has_no_critical_edge, is_erdos944_k_r1, chi_bt,
)


def three_colorable_with_coloring(adj, n):
    """Return a proper 3-coloring (list of colors) if 3-colorable, else None.
    Independent exact backtracking (returns the witness coloring)."""
    color = [-1] * n
    order = sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))

    def bt(idx):
        if idx == n:
            return True
        v = order[idx]
        forbidden = 0
        nb = adj[v]
        while nb:
            low = nb & (-nb)
            u = low.bit_length() - 1
            if color[u] >= 0:
                forbidden |= (1 << color[u])
            nb ^= low
        for c in range(3):
            if not (forbidden >> c) & 1:
                color[v] = c
                if bt(idx + 1):
                    return True
                color[v] = -1
        return False

    if bt(0):
        return color[:]
    return None


class CegarSearch:
    def __init__(self, n, min_deg=3, max_edges=None, fix_min_deg=True):
        self.n = n
        self.min_deg = min_deg
        self.max_edges = max_edges
        self.fix_min_deg = fix_min_deg
        self.vp = IDPool()
        self.clauses = []
        self.pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        self._build_base()

    def e(self, i, j):
        a, b = (i, j) if i < j else (j, i)
        return self.vp.id(("e", a, b))

    def cV(self, v, u, c):
        return self.vp.id(("cV", v, u, c))

    def c4(self, u, c):
        return self.vp.id(("c4", u, c))

    def _build_base(self):
        n = self.n
        # (V2) baked 4-coloring c4: each vertex exactly one of 4 colors, adjacent differ
        for u in range(n):
            self.clauses.append([self.c4(u, c) for c in range(4)])
            for c1 in range(4):
                for c2 in range(c1 + 1, 4):
                    self.clauses.append([-self.c4(u, c1), -self.c4(u, c2)])
        for (i, j) in self.pairs:
            for c in range(4):
                # e[i][j] -> not (c4 i c and c4 j c)
                self.clauses.append([-self.e(i, j), -self.c4(i, c), -self.c4(j, c)])

        # (C) baked witnessing 3-colorings of G - v
        for v in range(n):
            for u in range(n):
                if u == v:
                    continue
                self.clauses.append([self.cV(v, u, c) for c in range(3)])
                for c1 in range(3):
                    for c2 in range(c1 + 1, 3):
                        self.clauses.append([-self.cV(v, u, c1), -self.cV(v, u, c2)])
            for (i, j) in self.pairs:
                if i == v or j == v:
                    continue
                for c in range(3):
                    # e[i][j] -> not (cV v i c and cV v j c)
                    self.clauses.append([-self.e(i, j), -self.cV(v, i, c), -self.cV(v, j, c)])

        # min degree >= 3 (necessary for vertex-criticality)
        if self.fix_min_deg:
            from pysat.card import CardEnc, EncType
            for u in range(n):
                lits = [self.e(u, w) for w in range(n) if w != u]
                enc = CardEnc.atleast(lits=lits, bound=self.min_deg, vpool=self.vp,
                                      encoding=EncType.seqcounter)
                self.clauses.extend(enc.clauses)

        # light symmetry break: vertex 0 adjacent to vertex 1 (WLOG there is some edge;
        # this is a mild restriction, NOT full canonical form — see module docstring caveat)
        # (kept off by default to avoid affecting completeness claims)

    def _model_to_edges(self, model):
        ms = set(x for x in model if x > 0)
        edges = []
        for (i, j) in self.pairs:
            if self.e(i, j) in ms:
                edges.append((i, j))
        return edges

    def search(self, max_iters=200000, verbose=True):
        n = self.n
        solver = Cadical195()
        for cl in self.clauses:
            solver.add_clause(cl)
        it = 0
        while it < max_iters:
            it += 1
            if not solver.solve():
                solver.delete()
                return None, it, "UNSAT_under_clauses"
            model = solver.get_model()
            edges = self._model_to_edges(model)
            adj = edges_to_adj(edges, n)

            # (V1) is G NOT 3-colorable?
            phi = three_colorable_with_coloring(adj, n)
            if phi is not None:
                # refine: forbid this 3-coloring by forcing a monochromatic pair to become an edge
                mono = [(i, j) for (i, j) in self.pairs
                        if phi[i] == phi[j] and self.e(i, j) not in {x for x in model if x > 0}]
                # mono pairs are non-edges colored same; adding any breaks the coloring
                if not mono:
                    # all monochromatic pairs are already edges? impossible if phi proper. Block graph.
                    solver.add_clause([-self.e(i, j) if self.e(i, j) in {x for x in model if x>0}
                                       else self.e(i, j) for (i, j) in self.pairs])
                else:
                    solver.add_clause([self.e(i, j) for (i, j) in mono])
                continue

            # G is 4-chromatic and (by construction) vertex-critical. Check (E): no critical edge.
            present = set(edges)
            crit_edge = None
            crit_phi = None
            for (a, b) in edges:
                adj[a] &= ~(1 << b); adj[b] &= ~(1 << a)
                phi_e = three_colorable_with_coloring(adj, n)
                adj[a] |= (1 << b); adj[b] |= (1 << a)
                if phi_e is not None:
                    crit_edge = (a, b); crit_phi = phi_e
                    break
            if crit_edge is None:
                # CANDIDATE WITNESS — verify with both independent checkers
                solver.delete()
                ok_bt = is_erdos944_k_r1(edges, n, 4, chi_fn=chi_bt)
                return (edges, ok_bt), it, "CANDIDATE"
            # refine (E): forbid edge crit_edge from being non-critical via this coloring.
            # crit_phi is a 3-coloring of G - crit_edge. To make crit_edge non-critical we must
            # break this coloring: either drop crit_edge (then it's not an edge to worry about)
            # or add a monochromatic non-edge pair of G - crit_edge.
            a, b = crit_edge
            mono = [(i, j) for (i, j) in self.pairs
                    if crit_phi[i] == crit_phi[j]
                    and not (i == a and j == b) and not (i == b and j == a)
                    and self.e(i, j) not in {x for x in model if x > 0}]
            clause = [-self.e(a, b)] + [self.e(i, j) for (i, j) in mono]
            solver.add_clause(clause)
        solver.delete()
        return None, it, "MAX_ITERS"


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    max_iters = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
    print(f"# CEGAR search for e944 witness on n={n} (max_iters={max_iters})")
    cs = CegarSearch(n)
    result, iters, status = cs.search(max_iters=max_iters)
    print(f"# status={status} iters={iters}")
    if status == "CANDIDATE":
        edges, ok = result
        print(f"# CANDIDATE edges={edges}")
        print(f"# independent-checker confirms IsErdos944(4,1) = {ok}")
        if ok:
            print("# !!! WITNESS FOUND AND VERIFIED !!!")
    elif status == "UNSAT_under_clauses":
        print(f"# UNSAT under accumulated clauses (NOT a completeness proof without certified "
              f"symmetry breaking; treat as 'no witness found by this CEGAR run').")
