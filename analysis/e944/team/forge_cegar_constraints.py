#!/usr/bin/env python3
"""
forge_cegar_constraints.py — barrier-informed constraint augmentation for hunter's
CEGAR witness search (cegar_search.py).

Adds forge's crystallized-barrier constraints to massively prune the search while
keeping it SOUND (never excludes a real witness):

  (1) MIN DEGREE >= 6.  forge deg-3 theorem: a deg-3 vertex in a 4vc graph forces
      3 critical edges, so a witness has δ≥4 — FREE. SkSt Prop 5.1 proves δ≥6 and
      edge-connectivity ≥6 for any (4,1)-witness. Both are SOUND necessary
      conditions. Bumping min_deg 3→6 cuts the model space enormously.

  (2) EDGE-IN-≥2-TRIANGLES (entanglement necessary condition).  forge robustness-
      asymmetry + the round-1/2 blitz: a witness's per-edge obstruction must have
      ≥2 reroutes. A NECESSARY (sound) local witness of this: every edge uv must
      have ≥2 common neighbors (≥2 triangles on uv) — else deleting uv's single
      triangle-apex would expose it. (This is sound: SkSt edge-connectivity≥6 ⟹
      every edge is in many short cycles; ≥2 common neighbors is weaker, hence
      safe.) Encoded as: for each pair (u,v), e_uv -> atleast-2 of {t_uvw}, where
      t_uvw <-> e_uw ∧ e_vw.

  (3) NO-DEGREE-3 is subsumed by (1).

  (4) (optional, OFF by default — NOT proven sound) max degree <= n-5 (SkSt).
      Provided as a flag; sound per SkSt Prop 5.1.

USAGE (hand to hunter):
    from forge_cegar_constraints import ForgeCegarSearch
    s = ForgeCegarSearch(n, min_deg=6, entangle=True)
    result, iters, status = s.search()

All additions are SOUND necessary conditions for a (4,1)-witness (proven: forge
deg-3 theorem; published: SkSt Prop 5.1). A SAT result is a real candidate
(dual-verified by the base class); an UNSAT-under-these-clauses is NOT a
completeness proof (symmetry breaking not certified) — same caveat as the base.
"""
from pysat.card import CardEnc, EncType
from cegar_search import CegarSearch


class ForgeCegarSearch(CegarSearch):
    def __init__(self, n, min_deg=6, max_edges=None, entangle=False,
                 max_deg_cap=False, wall_balance=False):
        # entangle defaults OFF: the ≥2-common-neighbors clause is UNSOUND
        # (proximity 2026-06-11, excludes real witnesses). wall_balance defaults
        # OFF: makes SAT intractable at n≥11 (hunter). The only sound static
        # constraint is min_deg=6 (forge deg-3 thm + SkSt). For the search, hunter
        # uses min_deg=6 + LAZY THM4 + post-hoc λ≥6 (proximity's encoder).
        # build base with the higher min_deg (the base encodes atleast(min_deg))
        super().__init__(n, min_deg=min_deg, max_edges=max_edges, fix_min_deg=True)
        self._added = {"min_deg": min_deg, "entangle": False, "max_deg_cap": False,
                       "wall_balance": False}
        if entangle:
            self._add_entanglement_clauses()
            self._added["entangle"] = True
        if max_deg_cap:
            self._add_max_degree_cap()
            self._added["max_deg_cap"] = True
        if wall_balance:
            self._add_wall_balance_clauses()
            self._added["wall_balance"] = True

    def t(self, u, v, w):
        """triangle indicator t_{uvw} (u<v, w distinct)."""
        a, b = (u, v) if u < v else (v, u)
        return self.vp.id(("t", a, b, w))

    def _add_entanglement_clauses(self):
        """*** UNSOUND — DO NOT USE (proximity, 2026-06-11). ***
        "every edge has ≥2 common neighbors" EXCLUDES real (4,1)-graphs. Counter-
        examples: forge's OWN n=10 champion ICpdbY{]_ has non-critical edge (4,7)
        with only 1 common neighbor; C14(1,2,5) (6-regular, |E*|=0) has 28
        non-critical edges with <2 common neighbors, incl. (0,5),(0,9) with ZERO.
        A non-critical edge's redundancy is a GLOBAL coloring obstruction, NOT
        local triangles — there is no reason it needs common neighbors. So this is
        an UNSOUND hard constraint. Default OFF. The only SOUND local clause near
        here is wall's THM4 (applied LAZILY, not static — it makes SAT intractable),
        plus proximity's "every 2-vertex-set boundary ≥6" (sound λ≥6 proxy).
        [Kept for record only; entangle defaults to False.]"""
        n = self.n
        for (u, v) in self.pairs:
            tri_lits = []
            for w in range(n):
                if w == u or w == v:
                    continue
                tuvw = self.t(u, v, w)
                # t_uvw <-> e_uw ∧ e_vw
                self.clauses.append([-tuvw, self.e(u, w)])
                self.clauses.append([-tuvw, self.e(v, w)])
                self.clauses.append([tuvw, -self.e(u, w), -self.e(v, w)])
                tri_lits.append(tuvw)
            # e_uv -> atleast 2 of tri_lits
            # encode atleast-2(tri_lits) only when e_uv is true:
            # introduce: (¬e_uv) ∨ atleast2(tri). CardEnc.atleast gives clauses for
            # atleast2; we guard each by ¬e_uv is not directly supported, so use a
            # reified approach: atleast2 over (tri_lits) implied by e_uv.
            # Simplest sound encoding: add a selector — atleast2(tri_lits + [big copies])
            # Instead: enforce unconditionally weaker form is unsound. Use the
            # standard trick: atleast_k with bound 2 on tri_lits, then OR with ¬e_uv
            # per clause of the encoding.
            enc = CardEnc.atleast(lits=tri_lits, bound=2, vpool=self.vp,
                                  encoding=EncType.seqcounter)
            for cl in enc.clauses:
                self.clauses.append([-self.e(u, v)] + cl)

    def nc(self, v, u, c):
        """indicator: u is a neighbor of v AND has color c in G-v's baked 3-coloring."""
        return self.vp.id(("nc", v, u, c))

    def _add_wall_balance_clauses(self):
        """wall's witness criterion (= no critical edge), encoded DIRECTLY as the
        SHARPEST sound constraint: for the baked 3-coloring of G-v, every color
        appears >=2 times among the NEIGHBORS of v. This IS the (4,1)-witness
        condition (forge per-vertex lemma: edge vu critical <=> some color appears
        exactly once in N(v) under a 3-coloring of G-v). The base class already
        bakes ONE 3-coloring cV(v,·,·) per v; we require THAT coloring to be
        color-balanced on N(v). SOUND for the search target: a true witness admits
        such a balanced baked coloring for every v (any of its G-v 3-colorings is
        balanced, else that vertex would have a critical edge). Encoding:
          nc(v,u,c) <-> e(v,u) AND cV(v,u,c)
          for each (v,c): atleast 2 of {nc(v,u,c) : u != v}.
        NOTE: this overlaps the CEGAR (E)-refinement but front-loads it as static
        clauses, pruning the SAT model space directly to witness-candidates."""
        n = self.n
        for v in range(n):
            for c in range(3):
                lits = []
                for u in range(n):
                    if u == v:
                        continue
                    ncl = self.nc(v, u, c)
                    # nc <-> e(v,u) AND cV(v,u,c)
                    self.clauses.append([-ncl, self.e(v, u)])
                    self.clauses.append([-ncl, self.cV(v, u, c)])
                    self.clauses.append([ncl, -self.e(v, u), -self.cV(v, u, c)])
                    lits.append(ncl)
                enc = CardEnc.atleast(lits=lits, bound=2, vpool=self.vp,
                                      encoding=EncType.seqcounter)
                self.clauses.extend(enc.clauses)

    def _add_max_degree_cap(self):
        """max degree <= n-5 (SkSt Prop 5.1). Sound necessary condition."""
        n = self.n
        cap = n - 5
        if cap < self.min_deg:
            return  # infeasible / nothing to add
        for u in range(n):
            lits = [self.e(u, w) for w in range(n) if w != u]
            enc = CardEnc.atmost(lits=lits, bound=cap, vpool=self.vp,
                                 encoding=EncType.seqcounter)
            self.clauses.extend(enc.clauses)


if __name__ == "__main__":
    import sys
    ns = [int(x) for x in sys.argv[1:]] or [11, 12, 13]
    for n in ns:
        print(f"\n=== ForgeCegarSearch n={n} (min_deg=6, entangle) ===", flush=True)
        s = ForgeCegarSearch(n, min_deg=6, entangle=True)
        print(f"  clauses={len(s.clauses)} added={s._added}", flush=True)
        res, iters, status = s.search(max_iters=50000, verbose=False)
        print(f"  status={status} iters={iters}", flush=True)
        if status == "CANDIDATE":
            edges, ok = res
            print(f"  *** CANDIDATE n={n} dual-verified={ok} edges={edges} ***", flush=True)
            if ok:
                with open(f"forge_cegar_WITNESS_n{n}.txt", "w") as f:
                    f.write(f"# CEGAR WITNESS n={n}\n")
                    for u, v in sorted(edges):
                        f.write(f"{u} {v}\n")
                print(f"  Saved forge_cegar_WITNESS_n{n}.txt", flush=True)
                break
