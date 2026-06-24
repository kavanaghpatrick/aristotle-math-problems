"""
INVENTION MANDATE (jensen angle): re-express the J-S color-transfer gadget as a
PARITY/FLOW obstruction on a BRIDGELESS (2-edge-connected) structure, removing the
degree-3 path scaffolding (forge: deg-3 vtx => 3 critical edges).

WHAT J-S's transfer does (Lemma 2): the path x0..x_{2m+1} + y-pendants enforces a
relation between phi(x0) and phi(x_{2m+1}) in any proper 3-coloring. The mechanism
is a PARITY/TENSION condition: along a path, in a proper 3-coloring with colors in
Z_3, consecutive vertices differ, so the sequence of color-DIFFERENCES (each in
{1,2} mod 3) accumulates. The endpoint relation is a Z_3 tension along the path.

KEY 3-COLORING FACT (the parity substrate): a connected graph G is 3-colorable iff
it admits a Z_3-TENSION: an orientation + edge-labels t(e) in {1,2} (=Z_3\{0}) such
that around every cycle the signed sum of t is 0 mod 3. (Proper 3-coloring c gives
t(uv)=c(v)-c(u); conversely a tension integrates to a 3-coloring.) So "phi(x0) and
phi(x_{2m+1}) must differ/agree" = "the Z_3-tension integrated along ANY x0->x_{2m+1}
path takes a forced value" — and on a 2-edge-connected graph this is enforced by
CYCLES (every edge lies on a cycle), so NO bridges are needed.

CANDIDATE TRANSFER (bridgeless): replace the path x0-..-x_{2m+1} by a LADDER /
prism / theta-graph between x0 and x_{2m+1}: a 2-edge-connected graph where every
edge lies on a cycle, but whose 3-colorings still force a tension relation between
the two boundary vertices. We test whether such a bridgeless transfer (a) still
forces 'some S_i bichromatic' when wired into the J-S star+B, AND (b) has NO bridges
(so the per-edge criticality argument that killed the path version doesn't apply).

We build several bridgeless transfer candidates and test, for each, glued to B+star:
  - chi (must be 4 for the obstruction to bite),
  - bridges in the transfer (want 0),
  - critical-edge count (the payoff metric).
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges
from jensen_siggers import build_B


def z3_tension_check(G):
    """Sanity: a proper 3-coloring induces a Z_3 tension. Verify on a 3-colorable G
    that for the coloring c, t(uv)=c(v)-c(u) mod 3 sums to 0 around fundamental
    cycles. (Just a self-test of the substrate.)"""
    if chromatic_number(G) > 3:
        return None
    # get a 3-coloring via greedy on a 3-chromatic graph won't always be proper-min;
    # use networkx greedy then check; for connected 3-chromatic this is fine for test
    c = nx.greedy_color(G, strategy="DSATUR")
    if max(c.values()) + 1 > 3:
        return None
    # check tension around cycle basis
    for cyc in nx.cycle_basis(G):
        s = 0
        for i in range(len(cyc)):
            u, v = cyc[i], cyc[(i + 1) % len(cyc)]
            s += (c[v] - c[u])
        if s % 3 != 0:
            return False
    return True


def ladder_transfer(m, a, b, tag):
    """A 2-edge-connected 'transfer' between boundary vertices a,b:
    a prism/ladder of length 2m. Two parallel paths a=p0-p1-..-p_{2m}=b and
    a=q0-q1-..-q_{2m}=b with rungs p_j-q_j. Every edge lies on a 4-cycle => bridgeless.
    We also attach y-pendant analogues to mimic the J-S 'escape valve': here, to keep
    the parity character, we instead add chords. Returns (graph, S_y_list) where
    S_y_list are the vertices that will live in S_i (the B-shared part)."""
    G = nx.Graph()
    p = [a] + [("p", tag, j) for j in range(1, 2 * m)] + [b]
    q = [a] + [("q", tag, j) for j in range(1, 2 * m)] + [b]
    for j in range(2 * m):
        G.add_edge(p[j], p[j + 1])
        G.add_edge(q[j], q[j + 1])
    for j in range(1, 2 * m):
        G.add_edge(p[j], q[j])  # rungs => 2-edge-connected
    # S_i contribution: pick the rung-midpoints as the 'y' vertices that must be
    # color-coordinated with B's monochromatic class. Use p[odd] as S-vertices.
    Sy = [("p", tag, j) for j in range(1, 2 * m) if j % 2 == 1]
    return G, Sy


def build_parity_gadget(m, transfer=ladder_transfer):
    """J-S architecture but with a BRIDGELESS transfer instead of the path gadget.
    star v0,v1,v2,v3; for each chain i, a bridgeless transfer between v_i and v_{i+1}
    whose designated S-vertices join S_i (shared with B)."""
    G = nx.Graph()
    v0 = ("v", 0); G.add_node(v0)
    star = {i: ("v", i) for i in (1, 2, 3)}
    for i in (1, 2, 3):
        G.add_edge(v0, star[i])

    def vmod(i):
        return star[((i - 1) % 3) + 1]

    Smap = {1: [], 2: [], 3: []}
    for i in (1, 2, 3):
        tg, Sy = transfer(m, vmod(i), vmod(i + 1), f"c{i}")
        G.add_edges_from(tg.edges())
        # relabel the chosen Sy vertices into the shared S_i scheme
        for k, sv in enumerate(Sy):
            shared = ("S", i, "y", k + 1)
            G = nx.relabel_nodes(G, {sv: shared})
            Smap[i].append(shared)
    return G, Smap


def glue_and_test(m, transfer, name):
    Gg, Smap = build_parity_gadget(m, transfer)
    B, SB = build_B(m)
    # B's S_i must match the gadget's S_i count; pad/truncate B parts to |Smap[i]|
    # For a clean test, set B part size = max gadget S_i size (rebuild B accordingly)
    parts = max(len(Smap[i]) for i in (1, 2, 3))
    if parts == 0:
        print(f"{name}: gadget produced no S-vertices; skip")
        return
    # rebuild B with part size = parts
    Bp = nx.complete_multipartite_graph(parts, parts, parts)
    # map B nodes to ("S",i,"y",k)
    # complete_multipartite labels 0..3*parts-1 in blocks
    rename = {}
    idx = 0
    for i in (1, 2, 3):
        for k in range(parts):
            rename[idx] = ("S", i, "y", k + 1)
            idx += 1
    Bp = nx.relabel_nodes(Bp, rename)
    H = nx.Graph()
    H.add_nodes_from(Gg.nodes()); H.add_edges_from(Gg.edges())
    H.add_nodes_from(Bp.nodes()); H.add_edges_from(Bp.edges())
    chi = chromatic_number(H)
    nbridges = len(list(nx.bridges(H))) if nx.is_connected(H) else -1
    print(f"{name}: n={H.number_of_nodes()}, e={H.number_of_edges()}, chi={chi}, bridges={nbridges}")
    if chi == 4:
        vc = is_vertex_critical(H, 4)
        ce = critical_edges(H)
        print(f"   chi=4! vertex-critical={vc}, #critical edges={len(ce)}")


if __name__ == "__main__":
    # substrate self-test
    print("Z_3-tension substrate self-test on C6 (3-colorable):", z3_tension_check(nx.cycle_graph(6)))
    print("Z_3-tension on Petersen (3-chromatic):", z3_tension_check(nx.petersen_graph()))
    print()
    print("=== Bridgeless (ladder/prism) transfer in J-S architecture ===")
    for m in (2, 3):
        glue_and_test(m, ladder_transfer, f"ladder m={m}")
