"""
INVENTION BLITZ — jensen/parity lane, ROUND 1.
Design constraint: ENTANGLEMENT (dense, no separable rails). Several genuinely new
constructions; each built + scored with the harness (chi, vertex-crit, #critical edges).
Goal: 4-vertex-critical, 0 critical edges (a witness). Partial progress = low #critical
+ vertex-critical + dense.

Candidates (this lane, distinct from algebra's quasigroup/cover round):
  J1 Tension-monodromy wheel-web: ℤ₃-tension forced nonzero around MANY overlapping
     cycles (not one) -> dense, entangled, non-3-colorable by global tension.
  J2 Antiprism-stack / circular-ladder-with-diagonals: dense triangulated cylinder.
  J3 Complement of sparse triangle-free graph (dense, χ near 4, every edge in many triangles).
  J4 Kneser-like / Cayley-on-dihedral dense graph at the 4-chromatic boundary.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools, math
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def score(G, name):
    if not nx.is_connected(G):
        print(f"{name}: DISCONNECTED")
        return None
    n = G.number_of_nodes(); m = G.number_of_edges()
    chi = chromatic_number(G)
    dmin = min(d for _, d in G.degree())
    line = f"{name}: n={n} m={m} δ={dmin} χ={chi}"
    if chi == 4:
        vc = is_vertex_critical(G, 4)
        line += f" vtx-crit={vc}"
        if vc:
            ce = critical_edges(G)
            br = len(list(nx.bridges(G)))
            line += f" #critical={len(ce)} bridges={br}"
            if len(ce) == 0:
                line += "  *** WITNESS ***"
    print(line)
    return chi


# --- J1: tension-monodromy wheel-web ---
def J1_wheelweb(h, rim):
    """h hubs each joined to ALL rim vertices; rim is an odd cycle C_rim. Hubs
    pairwise adjacent. Dense, every rim edge in many triangles (hub-rim-rim)."""
    G = nx.Graph()
    rimv = list(range(rim))
    for i in range(rim):
        G.add_edge(("r", i), ("r", (i + 1) % rim))
    hubs = [("h", j) for j in range(h)]
    for a in range(h):
        for b in range(a + 1, h):
            G.add_edge(hubs[a], hubs[b])
        for i in range(rim):
            G.add_edge(hubs[a], ("r", i))
    return G


# --- J2: antiprism / circular ladder with diagonals (triangulated cylinder) ---
def J2_antiprism_stack(layers, w):
    """w-vertex cycles stacked in `layers`; consecutive layers joined as an antiprism
    (i~i and i~i+1 across layers) -> every quad becomes 2 triangles -> dense, entangled."""
    G = nx.Graph()
    for L in range(layers):
        for i in range(w):
            G.add_edge((L, i), (L, (i + 1) % w))
    for L in range(layers - 1):
        for i in range(w):
            G.add_edge((L, i), (L + 1, i))
            G.add_edge((L, i), (L + 1, (i + 1) % w))
    return G


# --- J3: complement of a sparse triangle-free graph ---
def J3_complement(n, base="cycle"):
    if base == "cycle":
        B = nx.cycle_graph(n)
    elif base == "petersen" and n == 10:
        B = nx.petersen_graph()
    else:
        B = nx.cycle_graph(n)
    return nx.complement(B)


# --- J4: Cayley graph of dihedral group D_k with a dense inverse-closed connection set ---
def J4_dihedral_cayley(k, conn):
    """D_k = <r,s | r^k, s^2, srs=r^-1>, elements (j,e) j in Z_k, e in {0,1}.
    conn: list of generators as (dj, de) pairs (inverse-closed)."""
    G = nx.Graph()
    elems = [(j, e) for j in range(k) for e in (0, 1)]
    G.add_nodes_from(elems)
    def mul(a, b):
        (j1, e1), (j2, e2) = a, b
        if e1 == 0:
            return ((j1 + j2) % k, e2)
        else:
            return ((j1 - j2) % k, 1 - e2)
    for a in elems:
        for g in conn:
            G.add_edge(a, mul(a, g))
    return G


if __name__ == "__main__":
    print("=== BLITZ ROUND 1 (jensen lane) ===")
    print("-- J1 wheel-web (h hubs + odd rim) --")
    for (h, rim) in [(2, 5), (3, 5), (2, 7), (3, 7)]:
        score(J1_wheelweb(h, rim), f"J1(h={h},rim={rim})")
    print("-- J2 antiprism stack --")
    for (L, w) in [(3, 4), (3, 5), (4, 4), (2, 6)]:
        score(J2_antiprism_stack(L, w), f"J2(layers={L},w={w})")
    print("-- J3 complement of cycle --")
    for n in (8, 9, 10, 11):
        score(J3_complement(n), f"J3(complement C_{n})")
    print("-- J4 dihedral Cayley --")
    # conn must be inverse-closed; (dj,0) inverse is (-dj,0); (dj,1) is its own inverse.
    score(J4_dihedral_cayley(6, [(1, 0), (5, 0), (0, 1), (2, 1), (4, 1)]), "J4(D6,c1)")
    score(J4_dihedral_cayley(7, [(1, 0), (6, 0), (0, 1), (1, 1), (3, 1)]), "J4(D7,c1)")
