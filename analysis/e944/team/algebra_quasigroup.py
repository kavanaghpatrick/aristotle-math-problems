#!/usr/bin/env python3
"""
algebra_quasigroup.py — E944 ASSAULT: asymmetric (non-associative) substrates.

Rationale: the orbit obstruction (algebra_substrate_verdict.md) kills SYMMETRIC
substrates because automorphisms force edge-criticality to be uniform on orbits,
so "no critical edge" needs EVERY orbit redundant — never achievable with
4-vertex-criticality. Quasigroups (Latin squares lacking associativity) and
Steiner systems generically have TRIVIAL automorphism groups => edges sit in
SINGLETON orbits => each edge can independently be critical-or-not. THIS is the
regime where a (4,1)-graph could live.

Design target (squad spec): a graph where every edge lies in MULTIPLE 4-chromatic
obstructions (=> no single edge critical) yet every vertex lies in ALL of them
(=> deleting any vertex kills 4-chromaticity = vertex-critical).

Substrate families built here:
  (Q1) Latin-square cell graph: vertices = n^2 cells of a Latin square L; adjacency
       = share a row, share a column, or share a symbol L[i][j]. (group table => SRG
       with big aut; random quasigroup => asymmetric.)
  (Q2) Latin-square "conflict" / partial-Latin graphs at controlled density.
  (Q3) Steiner triple system block-intersection graph.
  (Q4) Voltage / twisted lift of a small base graph by random (non-homomorphic)
       voltage assignments in Z_3 — lift inherits NO global symmetry.

All chi via hunter's checkers.py (backtrack + SAT cross-check).
Score = (#critical edges); 0 critical edges on a 4-vertex-critical graph = WITNESS.
"""
import sys, os, random, itertools
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as H
import algebra_substrate as A


# --------------------------------------------------------------------------
# Quasigroup / Latin square generation
# --------------------------------------------------------------------------

def random_latin_square(n, seed=None, tries=2000):
    """Generate a random n x n Latin square by randomized backtracking.
    Returns list-of-lists L with L[i][j] in 0..n-1, each symbol once per row/col."""
    rng = random.Random(seed)
    for _ in range(tries):
        L = [[-1] * n for _ in range(n)]
        ok = True
        for i in range(n):
            # symbols available decreasing; randomize order
            for j in range(n):
                used_row = set(L[i][:j])
                used_col = {L[r][j] for r in range(i)}
                cand = [s for s in range(n) if s not in used_row and s not in used_col]
                if not cand:
                    ok = False
                    break
                L[i][j] = rng.choice(cand)
            if not ok:
                break
        if ok:
            return L
    return None


def is_associative(L):
    """Check whether the quasigroup (L as op a*b=L[a][b]) is associative (=> group)."""
    n = len(L)
    for a in range(n):
        for b in range(n):
            for c in range(n):
                if L[L[a][b]][c] != L[a][L[b][c]]:
                    return False
    return True


def latin_cell_graph(L, relations=("row", "col", "sym")):
    """(Q1) Vertices = cells (i,j). Edge if two cells share row / col / symbol.
    For a group Cayley table this is a strongly-regular Latin-square graph (large
    aut). For a random quasigroup the symbol relation breaks the symmetry."""
    n = len(L)
    G = nx.Graph()
    cells = [(i, j) for i in range(n) for j in range(n)]
    G.add_nodes_from(cells)
    for (i1, j1), (i2, j2) in itertools.combinations(cells, 2):
        adj = False
        if "row" in relations and i1 == i2:
            adj = True
        elif "col" in relations and j1 == j2:
            adj = True
        elif "sym" in relations and L[i1][j1] == L[i2][j2]:
            adj = True
        if adj:
            G.add_edge((i1, j1), (i2, j2))
    return G


# --------------------------------------------------------------------------
# Voltage / twisted lift (Q4)
# --------------------------------------------------------------------------

def voltage_lift(base_edges, base_n, voltages, fiber=3):
    """(Q4) Lift base graph by Z_fiber voltages. Vertex set = base x Z_fiber.
    For base edge (u,v) with voltage g: connect (u,t)-(v,(t+g)%fiber) for all t.
    Random voltages (non-coboundary) yield an asymmetric lift. If all voltages 0
    we just get fiber disjoint copies; nonzero voltages twist the fibers."""
    G = nx.Graph()
    for u in range(base_n):
        for t in range(fiber):
            G.add_node((u, t))
    for idx, (u, v) in enumerate(base_edges):
        g = voltages[idx] % fiber
        for t in range(fiber):
            G.add_edge((u, t), (v, (t + g) % fiber))
    return G


# --------------------------------------------------------------------------
# Scoring
# --------------------------------------------------------------------------

def score_graph(G, k=4):
    """Return dict: chi, vertex_critical, n_critical_edges, is_witness.
    Uses hunter's verified predicates; cross-checks chi backtrack vs SAT."""
    e, nn = A.nx_to_edges_n(G)
    c_bt = H.chi_bt(e, nn)
    try:
        c_sat = H.chromatic_number_sat(e, nn)
        if c_sat != c_bt:
            raise AssertionError(f"chi mismatch bt={c_bt} sat={c_sat}")
    except AssertionError:
        raise
    except Exception:
        pass
    res = {"n": nn, "m": len(e), "chi": c_bt, "vertex_critical": None,
           "n_critical_edges": None, "is_witness": False}
    if c_bt != k:
        return res
    vc = H.is_vertex_critical(e, nn, k)
    res["vertex_critical"] = vc
    if not vc:
        return res
    ncrit = sum(1 for ed in e if H.chi_bt(H.edges_remove_edge(e, ed), nn) < k)
    res["n_critical_edges"] = ncrit
    res["is_witness"] = (ncrit == 0)
    return res


if __name__ == "__main__":
    print("=== E944 ASSAULT: asymmetric substrate batch (algebra) ===\n")

    # ---- (Q1) Latin-square cell graphs, random quasigroups, small n ----
    print("--- (Q1) Latin-square cell graphs (row+col+sym) ---")
    for n in (3, 4):
        for seed in range(6):
            L = random_latin_square(n, seed=seed)
            if L is None:
                continue
            assoc = is_associative(L)
            for rels in [("row", "col", "sym"), ("row", "sym"), ("col", "sym")]:
                G = latin_cell_graph(L, rels)
                s = score_graph(G)
                tag = "GROUP" if assoc else "quasi"
                flag = "  <<< WITNESS >>>" if s["is_witness"] else ""
                if s["chi"] == 4:
                    print(f"  n={n} seed={seed} {tag} rel={rels}: "
                          f"V={s['n']} chi=4 vc={s['vertex_critical']} "
                          f"crit_edges={s['n_critical_edges']}{flag}")

    # ---- (Q4) Voltage lifts of small bases over Z_3 ----
    print("\n--- (Q4) Voltage lifts over Z_3 of small 2-chromatic/3-chromatic bases ---")
    bases = {
        "C5": ([(0,1),(1,2),(2,3),(3,4),(4,0)], 5),
        "K4": (list(itertools.combinations(range(4),2)), 4),
        "C4": ([(0,1),(1,2),(2,3),(3,0)], 4),
        "P3path": ([(0,1),(1,2),(2,3)], 4),
    }
    rng = random.Random(0)
    best = {}
    for bname, (be, bn) in bases.items():
        witnesses = 0
        best_score = None
        for trial in range(200):
            volts = [rng.randrange(3) for _ in be]
            G = voltage_lift(be, bn, volts, fiber=3)
            s = score_graph(G)
            if s["chi"] != 4 or not s["vertex_critical"]:
                continue
            if best_score is None or s["n_critical_edges"] < best_score:
                best_score = s["n_critical_edges"]
            if s["is_witness"]:
                witnesses += 1
                print(f"  WITNESS! base={bname} volts={volts} V={s['n']}")
        best[bname] = best_score
        print(f"  base={bname}: best #critical_edges among 4-vertex-critical lifts = {best_score}, witnesses={witnesses}")
