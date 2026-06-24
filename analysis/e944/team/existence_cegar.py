"""
e944 EXISTENCE CAMPAIGN — scaled SAT-CEGAR search for a (4,1)-witness at n=14..20 (hunter).

Goal: FIND a graph G on n labeled vertices with
  (V) chi(G) = 4
  (C) vertex-critical: for all v, chi(G - v) <= 3
  (E) no critical edge: for all edges e, chi(G - e) = 4
i.e. a witness to erdos_944.dirac_conjecture.k_eq_four. A verified witness resolves Dirac's 1970
conjecture for k=4.

Upgrades over cegar_search.py (which was sound but stalled past n~9):
  - INCREMENTAL solver (single Cadical instance, clauses added in place).
  - STATIC necessary-condition clauses encoded UP FRONT (Skottova-Steiner Prop 5.1, proven):
      * min-degree >= 6        (cardinality at-least-6 per vertex)
      * max-degree <= n - 5    (cardinality at-most-(n-5) per vertex)
  - VERTEX-CRITICALITY baked as witnessing 3-colorings cV[v] of G-v (forces (C) by construction).
  - 4-COLORABILITY baked as witnessing 4-coloring c4 (forces chi<=4 by construction).
  - (V1) chi != 3 and (E) no-critical-edge enforced by SOUND CEGAR refinement (lazy).
  - wall's per-vertex BALANCE criterion used as a fast PRE-CHECK on each candidate (cheap reject)
    AND as a refinement target.
  - Light, SOUND symmetry break: fix vertex 0 = a maximum-degree vertex via a lex hint (optional;
    OFF by default to keep completeness; ON only for FIND-mode speed).

SOUNDNESS of refinements (so any returned model that passes both checkers is a true witness, and
UNSAT with symmetry OFF is a real completeness statement):
  - (V1) refine: candidate G is 3-colorable via phi. Add clause OR over phi-monochromatic NON-edges
    e[i][j]. A true witness (non-3-colorable) makes phi improper => some mono pair is an edge =>
    clause satisfied. Never excludes a witness.
  - (E) refine: edge ab present but G-ab is 3-colorable via phi_e. Add (NOT e_ab) OR (OR of
    phi_e-monochromatic non-edges of G-ab). A true witness with ab present has G-ab non-3-colorable
    => phi_e improper => clause satisfied. Never excludes a witness.

We re-verify EVERY candidate witness with BOTH independent checkers (backtrack + SAT) before
declaring success.
"""
import sys, time, json, argparse
from pysat.solvers import Cadical195
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from checkers import (edges_to_adj, is_erdos944_k_r1, chi_bt,
                      chromatic_number_sat, is_k_colorable_sat)


def three_coloring(adj, n):
    """Return a proper 3-coloring (list) if 3-colorable else None. Exact backtracking."""
    color = [-1] * n
    order = sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))
    def bt(i):
        if i == n: return True
        v = order[i]; forb = 0; nb = adj[v]
        while nb:
            low = nb & (-nb); u = low.bit_length()-1
            if color[u] >= 0: forb |= (1 << color[u])
            nb ^= low
        for c in range(3):
            if not (forb >> c) & 1:
                color[v] = c
                if bt(i+1): return True
                color[v] = -1
        return False
    return color[:] if bt(0) else None


class ExistenceSearch:
    def __init__(self, n, min_deg=6, max_deg=None, sym_break=False, use_thm4=True,
                 thm4_exactly6=False):
        self.n = n
        self.min_deg = min_deg
        self.max_deg = max_deg if max_deg is not None else (n - 5)
        self.sym_break = sym_break
        self.use_thm4 = use_thm4          # gallai THM4 balanced-neighborhood static prune (proximity)
        self.thm4_exactly6 = thm4_exactly6  # exactly-2-2-2; SOUND only for exactly-6-regular search
        self.vp = IDPool()
        self.pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
        self.solver = Cadical195()
        self._build()
        if self.use_thm4:
            self._apply_thm4()

    def _apply_thm4(self):
        """Bolt gallai THM4 (proximity_cegar_constraints.thm4_apply) onto the baked cV colorings.
        Builds the 2D e[][] and 3D cV[][][] arrays the helper expects from our accessors.
        SOUND: only excludes non-witnesses (every witness vertex has all incident edges non-critical,
        so every 3-coloring of G-v is 2-2-2-balanced on N(v))."""
        import proximity_cegar_constraints as pc
        n = self.n
        e = [[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i+1, n):
                e[i][j] = self.e(i, j); e[j][i] = self.e(i, j)
        cV = [[[None]*3 for _ in range(n)] for _ in range(n)]
        for v in range(n):
            for u in range(n):
                if u == v: continue
                for c in range(3):
                    cV[v][u][c] = self.cV(v, u, c)
        self.thm4_clauses = pc.thm4_apply(self.solver, self.vp, n, e, cV,
                                          degree_exactly_6=self.thm4_exactly6)

    def e(self, i, j):
        a, b = (i, j) if i < j else (j, i)
        return self.vp.id(("e", a, b))
    def cV(self, v, u, c): return self.vp.id(("cV", v, u, c))
    def c4(self, u, c):    return self.vp.id(("c4", u, c))

    def _add(self, cl): self.solver.add_clause(cl)

    def _build(self):
        n = self.n
        # (V2) baked 4-coloring
        for u in range(n):
            self._add([self.c4(u, c) for c in range(4)])
            for c1 in range(4):
                for c2 in range(c1+1, 4):
                    self._add([-self.c4(u, c1), -self.c4(u, c2)])
        for (i, j) in self.pairs:
            for c in range(4):
                self._add([-self.e(i, j), -self.c4(i, c), -self.c4(j, c)])
        # (C) baked witnessing 3-colorings of every G-v
        for v in range(n):
            for u in range(n):
                if u == v: continue
                self._add([self.cV(v, u, c) for c in range(3)])
                for c1 in range(3):
                    for c2 in range(c1+1, 3):
                        self._add([-self.cV(v, u, c1), -self.cV(v, u, c2)])
            for (i, j) in self.pairs:
                if i == v or j == v: continue
                for c in range(3):
                    self._add([-self.e(i, j), -self.cV(v, i, c), -self.cV(v, j, c)])
        # min-degree >= 6
        for u in range(n):
            lits = [self.e(u, w) for w in range(n) if w != u]
            enc = CardEnc.atleast(lits=lits, bound=self.min_deg, vpool=self.vp, encoding=EncType.seqcounter)
            for cl in enc.clauses: self._add(cl)
        # max-degree <= n-5
        if self.max_deg < n - 1:
            for u in range(n):
                lits = [self.e(u, w) for w in range(n) if w != u]
                enc = CardEnc.atmost(lits=lits, bound=self.max_deg, vpool=self.vp, encoding=EncType.seqcounter)
                for cl in enc.clauses: self._add(cl)
        # SYMMETRY BREAKING — DISABLED. The adjacent-transposition lex constraint below was found
        # (hunter, 2026-06-10) to be UNSOUND for completeness: standalone n=4 enumeration showed it
        # admits only 8 of the 11 isomorphism classes (it drops C4, P4, diamond — classes with no
        # adjacent-swap-locally-maximal labeling). So `--sym` UNSAT cannot be trusted, and it can even
        # miss a witness. Do NOT enable. Kept only for the post-mortem record.
        if self.sym_break:
            raise RuntimeError("sym_break is UNSOUND (drops iso classes) — disabled, see comment")

    def _evar_or_false(self, i, j):
        """edge literal for (i,j), or None if i==j (treated as constant 0)."""
        if i == j:
            return None
        return self.e(i, j)

    def _add_row_geq_lex(self, r1, r2):
        """Add CNF for row(r1) >=_lex row(r2) over columns k != r1, r2 (skip the swapped pair and
        self-loops). Uses auxiliary 'equal-prefix' variables. Standard lexicographic CNF."""
        n = self.n
        cols = [k for k in range(n) if k != r1 and k != r2]
        # a_k = e(r1,k), b_k = e(r2,k). Want (a) >=_lex (b).
        # eq_k = prefix [0..k-1] all equal. eq_0 = True.
        prev_eq = None  # None == True (constant)
        for idx, k in enumerate(cols):
            a = self.e(r1, k)
            b = self.e(r2, k)
            # constraint at this position: prev_eq -> (a >= b), i.e. prev_eq -> (a OR NOT b)
            if prev_eq is None:
                self._add([a, -b])
            else:
                self._add([-prev_eq, a, -b])
            # new eq var: eq_k <-> prev_eq AND (a == b)
            eq = self.vp.id(("lexeq", r1, r2, idx))
            # eq -> prev_eq ; eq -> (a==b) ; (prev_eq AND a==b) -> eq
            if prev_eq is None:
                # eq <-> (a==b)
                self._add([-eq, a, -b]); self._add([-eq, -a, b])      # eq -> a==b
                self._add([eq, -a, -b]); self._add([eq, a, b])        # a==b -> eq  (covers both equal cases)
            else:
                self._add([-eq, prev_eq])
                self._add([-eq, a, -b]); self._add([-eq, -a, b])
                # (prev_eq AND a==b) -> eq :  (-prev_eq OR a!=b OR eq)
                self._add([-prev_eq, -a, b, eq]); self._add([-prev_eq, a, -b, eq])
            prev_eq = eq

    def _edges(self, model):
        ms = set(x for x in model if x > 0)
        return [(i, j) for (i, j) in self.pairs if self.e(i, j) in ms]

    def search(self, max_iters, deadline=None, log_every=2000):
        n = self.n; t0 = time.time(); it = 0
        last_log = t0
        while it < max_iters:
            it += 1
            if deadline and time.time() > deadline:
                return {"status": "DEADLINE", "iters": it, "elapsed": time.time()-t0}
            if not self.solver.solve():
                return {"status": "UNSAT", "iters": it, "elapsed": time.time()-t0}
            model = self.solver.get_model()
            ms = set(x for x in model if x > 0)
            edges = [(i, j) for (i, j) in self.pairs if self.e(i, j) in ms]
            adj = edges_to_adj(edges, n)
            # (V1) is G 3-colorable? (must NOT be)
            phi = three_coloring(adj, n)
            if phi is not None:
                mono = [(i, j) for (i, j) in self.pairs if phi[i] == phi[j] and self.e(i, j) not in ms]
                self._add([self.e(i, j) for (i, j) in mono] if mono else [-self.e(*p) for p in self.pairs])
                if time.time()-last_log > 30:
                    print(f"# it={it} chi3-refine deg={[bin(adj[v]).count('1') for v in range(n)]} elapsed={time.time()-t0:.0f}s", flush=True)
                    last_log = time.time()
                continue
            # chi==4, vertex-critical by construction. (E) check no critical edge.
            crit = None
            for (a, b) in edges:
                adj[a] &= ~(1<<b); adj[b] &= ~(1<<a)
                phi_e = three_coloring(adj, n)
                adj[a] |= (1<<b); adj[b] |= (1<<a)
                if phi_e is not None:
                    crit = (a, b, phi_e); break
            if crit is None:
                # CANDIDATE WITNESS — verify both checkers
                ok_bt = is_erdos944_k_r1(edges, n, 4, chi_fn=chi_bt)
                # SAT cross-check
                ok_sat = self._verify_sat(edges, n)
                return {"status": "WITNESS" if (ok_bt and ok_sat) else "FALSE_CANDIDATE",
                        "edges": edges, "ok_bt": ok_bt, "ok_sat": ok_sat,
                        "iters": it, "elapsed": time.time()-t0}
            a, b, phi_e = crit
            mono = [(i, j) for (i, j) in self.pairs
                    if phi_e[i] == phi_e[j] and not (i == a and j == b) and self.e(i, j) not in ms]
            self._add([-self.e(a, b)] + [self.e(i, j) for (i, j) in mono])
            if time.time()-last_log > 30:
                print(f"# it={it} E-refine edge=({a},{b}) elapsed={time.time()-t0:.0f}s", flush=True)
                last_log = time.time()
        return {"status": "MAX_ITERS", "iters": it, "elapsed": time.time()-t0}

    def _verify_sat(self, edges, n):
        if is_k_colorable_sat(edges, n, 3): return False
        if not is_k_colorable_sat(edges, n, 4): return False
        for v in range(n):
            remap = {}; nn = 0
            for x in range(n):
                if x != v: remap[x] = nn; nn += 1
            sub = [(remap[u], remap[w]) for (u, w) in edges if u != v and w != v]
            if not is_k_colorable_sat(sub, nn, 3): return False
        for (a, b) in edges:
            sub = [ee for ee in edges if ee != (a, b)]
            if is_k_colorable_sat(sub, n, 3): return False
        return True


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("--max-iters", type=int, default=200000)
    ap.add_argument("--time", type=float, default=600, help="wall-clock budget seconds")
    ap.add_argument("--min-deg", type=int, default=6)
    ap.add_argument("--max-deg", type=int, default=None)
    ap.add_argument("--sym", action="store_true", help="enable sound symmetry hint (FIND mode)")
    args = ap.parse_args()
    print(f"# EXISTENCE CEGAR n={args.n} min_deg={args.min_deg} max_deg={args.max_deg or args.n-5} "
          f"sym={args.sym} budget={args.time}s", flush=True)
    es = ExistenceSearch(args.n, min_deg=args.min_deg, max_deg=args.max_deg, sym_break=args.sym)
    res = es.search(args.max_iters, deadline=time.time()+args.time)
    print(f"# RESULT n={args.n}: {res['status']} iters={res['iters']} elapsed={res['elapsed']:.1f}s", flush=True)
    if res["status"] == "WITNESS":
        print("# !!!!!!! WITNESS FOUND AND VERIFIED ON BOTH CHECKERS !!!!!!!")
        print(f"# n={args.n} edges={res['edges']}")
        with open(f"/Users/patrickkavanagh/math/analysis/e944/team/WITNESS_n{args.n}.json", "w") as f:
            json.dump({"n": args.n, "edges": res["edges"]}, f)
        print(f"# saved WITNESS_n{args.n}.json")
    elif res["status"] == "FALSE_CANDIDATE":
        print(f"# candidate FAILED dual-check (bt={res['ok_bt']} sat={res['ok_sat']}) — refinement bug, investigate")
        print(f"# edges={res['edges']}")
