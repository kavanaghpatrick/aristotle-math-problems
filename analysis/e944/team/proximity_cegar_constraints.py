"""
Constraint-engineering helpers for hunter's existence_cegar.py (proximity).

Answers hunter's 3 questions with concrete, SOUND clause generators that bolt onto his encoding:
  e[i][j]  = edge indicator vars
  cV[v][u][c] = baked 3-coloring of G-v: vertex u (u!=v) gets color c in {0,1,2}
  c4[u][c] = baked 4-coloring of G (witnessing 4-colorability), c in {0,1,2,3}

All generators return lists of clauses (lists of int literals) to add to the solver. Every
constraint is SOUND for the witness search: it can only exclude graphs that are NOT (4,1)-witnesses,
because a true witness provably satisfies it. Soundness justification given per function.

================================================================================================
Q3 (HIGHEST VALUE) — gallai THM4: forced 2-2-2 balanced neighborhoods, as STATIC clauses on cV.
================================================================================================
THM4 (PROVEN by gallai, validated by me on C13(1,2,5)): in any (4,1)-witness, for every vertex v
and EVERY proper 3-coloring of G-v, the neighborhood N(v) uses all 3 colors with each color class
of size >= 2. For a degree-6 vertex that means EXACTLY 2-2-2.

SOUNDNESS: THM4's hypothesis is "every incident edge of v is non-critical", which holds for EVERY
vertex of a witness (a witness has NO critical edge). So imposing 2-2-2 on the baked coloring cV[v]
excludes only non-witnesses. Validated: on C13(1,2,5) (which HAS critical edges) the non-2-2-2
colorings occur exactly at vertices incident to critical edges -- consistent, and absent in a witness.

Since hunter BAKES one coloring cV[v] per vertex (forcing vertex-criticality), we add to that SAME
baked coloring the constraint "the 6 neighbors of v are split 2-2-2". But the neighbor SET depends on
the edge variables (we're searching the graph!), so the clause must be conditional on which vertices
are neighbors. Encoding below handles that with the edge vars as guards.
"""
from itertools import combinations


def thm4_balanced_neighborhood_clauses(n, e, cV, pool, degree=6):
    """Q3. For each vertex v and its baked 3-coloring cV[v], force: among the neighbors of v
    (the u with e[v][u] true), each color class has size >= 2 (hence exactly 2-2-2 at degree 6).

    We use the equivalent 'no color class of size <= 1' form, which is what THM4 forbids:
    for every vertex v, every color c in {0,1,2}, it is NOT the case that exactly 0 or exactly 1
    neighbor of v has color c in cV[v].

    Encoding (size>=2 per color, conditioned on the edge being present):
      For color c and vertex v: introduce count of {u != v : e[v][u] AND cV[v][u]==c}.
      "count >= 2 OR count == 0" is the safe form... but THM4 actually requires count >= 2 for
      colors that appear at all, and all 3 colors DO appear (the neighborhood is 3-chromatic-free
      but spans 3 colors since deg=6>=3 forces it). So the clean witness constraint at deg-EXACTLY-6
      is: each of the 3 colors appears on >= 2 neighbors, i.e. >= 2 AND <= 2 = exactly 2.

    We emit, per (v, c): a cardinality constraint that the literals {y_{v,u,c}} (= e[v][u] ∧ cV[v][u]=c)
    sum to >= 2 and <= 2, but ONLY valid when deg(v)=6. Since the search fixes degree window, when
    the model has deg(v)=6 we impose exactly-2; we condition with the degree.

    For simplicity and to keep it SOUND under any degree in [6, n-5], we impose the WEAKER but always
    sound 'each color class >= 2' (THM4's general statement), via auxiliary AND-vars. At degree 6 this
    is equivalent to 2-2-2.
    """
    clauses = []
    aux = {}   # y[(v,u,c)] <-> e[v][u] AND cV[v][u]==c
    for v in range(n):
        for c in range(3):
            ylits = []
            for u in range(n):
                if u == v:
                    continue
                ev = e[min(v, u)][max(v, u)]
                cvar = cV[v][u][c]
                y = pool.id(("thm4y", v, u, c))
                # y <-> ev AND cvar
                clauses.append([-y, ev])
                clauses.append([-y, cvar])
                clauses.append([y, -ev, -cvar])
                ylits.append(y)
                aux[(v, u, c)] = y
            # each color class of v's neighborhood has size >= 2:  sum(ylits) >= 2.
            # "at least 2 of ylits true" = for every single literal y_i, the rest must contain >=1 more,
            # encoded simply via the standard 'atleast 2' through pairwise-at-most-(k-1) negation is
            # expensive; instead caller should use CardEnc.atleast(ylits, 2). We return the y-defs and
            # let the caller add the cardinality (it has the IDPool). We signal via a marker tuple.
            clauses.append(("ATLEAST2", ylits))
    return clauses


def thm4_apply(solver, pool, n, e, cV, degree_exactly_6=False):
    """Convenience: build THM4 y-vars + add 'each neighborhood color class >= 2' (and <=2 if
    degree fixed at 6) directly to `solver`. Returns number of clauses added.

    *** SOUNDNESS WARNING on degree_exactly_6 ***
    THM4 (general, all degrees) = "each of the 3 color classes in N(v) has size >= 2". This is the
    SOUND default for ANY min-deg-6 search (atleast-2 only).
    degree_exactly_6=True ALSO adds atmost-2, forcing EXACTLY 2-2-2. That is sound ONLY if every
    vertex has degree EXACTLY 6 (an exactly-6-regular search, geng -d6 -D6). On a general min-deg-6
    search (degrees up to n-5), a witness MAY have a degree-7 vertex with neighborhood 3-2-2 — and
    exactly-2-2-2 would WRONGLY exclude it. So set degree_exactly_6=True ONLY for exactly-6-regular.
    Default is False (the always-sound atleast-2 form). [proximity, soundness fix]"""
    from pysat.card import CardEnc, EncType
    added = 0
    for v in range(n):
        for c in range(3):
            ylits = []
            for u in range(n):
                if u == v:
                    continue
                ev = e[min(v, u)][max(v, u)]
                cvar = cV[v][u][c]
                y = pool.id(("thm4y", v, u, c))
                for cl in ([-y, ev], [-y, cvar], [y, -ev, -cvar]):
                    solver.add_clause(cl); added += 1
                ylits.append(y)
            for cl in CardEnc.atleast(ylits, bound=2, vpool=pool,
                                      encoding=EncType.seqcounter).clauses:
                solver.add_clause(cl); added += 1
            if degree_exactly_6:
                for cl in CardEnc.atmost(ylits, bound=2, vpool=pool,
                                         encoding=EncType.seqcounter).clauses:
                    solver.add_clause(cl); added += 1
    return added


# ================================================================================================
# Q1 — edge-connectivity >= 6 as a SOUND static relaxation.
# ================================================================================================
# Full "every cut >= 6" is exponential. But min-degree >= 6 (already encoded) gives lambda >= ... not
# automatically 6. The cheap SOUND static prune that strengthens degree:
#   (a) NO two vertices u,v with a 'separating pair pattern' ... still global.
# The PRACTICAL sound static layer: forbid small EDGE cuts that isolate a SMALL vertex set T
# (|T| <= 3), because such a cut would have size = (edges leaving T). For |T|=1 this is just
# degree>=6 (already have it). For |T|=2: the two vertices in T have together >= 12 incident
# edge-endpoints, minus 2*(edges inside T) <= 2; edges leaving T = deg(a)+deg(b) - 2*[ab edge]
# - 2*(common structure)... cleanest SOUND clause: for every pair {a,b}, (edges from {a,b} to
# outside) >= 6. That is a cardinality over the boundary edge-vars. We provide it; it's O(n^2)
# cardinality constraints, cheap, and SOUND (a (4,1)-graph has lambda>=6 so every 2-set boundary >=6
# UNLESS the 2-set is the whole small side -- but |V|>=11 so a 2-set is never a full side).
def edge_connectivity_2set_clauses(solver, pool, n, e):
    """Q1 partial: for every 2-subset T={a,b}, the number of edges from T to V\\T is >= 6.
    SOUND for a (4,1)-graph (lambda>=6, and |V|>=11 means T is always the small side of a cut).
    boundary(T) = [e[a][w] for w not in T] + [e[b][w] for w not in T]. >= 6."""
    from pysat.card import CardEnc, EncType
    added = 0
    for a, b in combinations(range(n), 2):
        blits = []
        for w in range(n):
            if w == a or w == b:
                continue
            blits.append(e[min(a, w)][max(a, w)])
            blits.append(e[min(b, w)][max(b, w)])
        for cl in CardEnc.atleast(blits, bound=6, vpool=pool,
                                  encoding=EncType.seqcounter).clauses:
            solver.add_clause(cl); added += 1
    return added
# NOTE: 3-set boundary clauses are analogously sound and add another O(n^3) layer; add only if the
# 2-set layer doesn't prune enough. lambda>=6 should still be verified post-hoc (networkx) since these
# static clauses only cover small cuts, not arbitrary ones.


# ================================================================================================
# Q2 — tighter vertex-criticality: which baked colorings can be dropped / CEGAR'd.
# ================================================================================================
# hunter bakes a full 3-coloring cV[v] for ALL n vertices (3n^2 vars). Observations to shrink it:
#
# 1. SOUNDNESS REQUIRES coverage of all v eventually, but you can CEGAR the colorings: start with NO
#    baked colorings; the structural model proposes a graph; verify vertex-criticality with checkers;
#    if some vertex v is NOT critical, that's a refutation -> add a baked cV[v] (or just block the
#    graph). This trades a huge static instance for incremental lazy colorings. For the witness search
#    where MOST structural graphs fail vertex-criticality fast, lazy is far smaller per-iteration.
#
# 2. If you keep baked colorings: by the cyclic/automorphism symmetry of your canonical-form breaking,
#    you only need to bake colorings for ONE representative per vertex-orbit. But computing the orbit
#    needs the graph (unknown), so this only helps for vertex-transitive sub-searches (e.g. circulant,
#    which proximity already CLOSED n<=19 -- don't bother).
#
# 3. The cheapest sound shrink: bake cV[v] only for v in a DOMINATING-ish anchor set is NOT sound
#    (criticality is per-vertex). So: either all-baked (big, complete) or fully-lazy CEGAR (small,
#    same completeness via refinement). Recommend FULLY-LAZY for the witness search; keep all-baked
#    only if you want a single monolithic UNSAT certificate per n.
#
# RECOMMENDED COMBO for hunter: lazy vertex-criticality (drop baked cV entirely; CEGAR it) +
# THM4 2-2-2 as static clauses on the c4 4-coloring's RESTRICTION... but THM4 is about 3-colorings of
# G-v, so it needs at least the cV[v] for vertices you want to prune. Pragmatic: bake cV[v] for all v
# (as now) AND add THM4 2-2-2 on them -> the 2-2-2 constraint makes each baked coloring HIGHLY
# constrained, which actually SPEEDS unit propagation (fewer feasible colorings), often net faster
# despite the var count. Try THM4-on-baked first; if instance too big, go lazy.
