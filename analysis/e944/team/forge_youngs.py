#!/usr/bin/env python3
"""
forge_youngs.py — verify-then-exploit Youngs' theorem as a candidate SECOND
non-vertex-aligned global redundancy mechanism for E944 k=4.

Youngs (1996): every NON-BIPARTITE quadrangulation of the projective plane is
EXACTLY 4-chromatic (never 3). The obstruction is a global ℤ₂ invariant (the
quadrangulation is "odd"), NOT any local odd cycle or clique. This is exactly the
"global, non-vertex-aligned" property the invention mandate wants.

CENTRAL QUESTION: in a vertex-critical non-bipartite projective quadrangulation,
does the parity obstruction survive every SINGLE-edge deletion (=> no critical
edge => witness)? Or does deleting an edge break the quadrangulation enough to
allow a 3-coloring (=> critical edge)?

We construct projective-plane quadrangulations as ANTIPODAL QUOTIENTS of
centrally-symmetric quadrangulations of the SPHERE (S^2). A centrally symmetric
quadrangulation Q of S^2 with antipodal map a (free involution) quotients to a
quadrangulation of RP^2 = S^2 / a. Non-bipartite iff ... we just test parity.

Simplest family: the "cylinder/prism" quadrangulations. Take the prism-like grid
C_{2k} x P_2 (a 2k-antiprism-ish quadrangulation of the sphere) with antipodal
identification. We build several and TEST: chi, vertex-criticality, critical edges.

We ALSO build the canonical small ones directly:
 - The complete bipartite-ish 'pseudo-double-wheel' / and known smallest
   non-bipartite projective quadrangulations.
We rely on EXACT chi (forge_verify + checkers), not on the embedding theory, to
confirm chi=4. The embedding only motivates the family.
"""
import itertools
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers


def antipodal_quotient_prism(k):
    """
    Build a quadrangulation of RP^2 from a 'Mobius-Kantor'-style construction:
    vertices Z_{2k} on a cycle, plus chords, with antipodal identification i ~ i+k.
    Concretely: the Mobius ladder / and odd analogs. We construct the
    'cyclic quadrangulation' Q(k): vertices 0..2k-1 in a cycle C_{2k}, plus the
    antipodal 'diameter' edges i -- i+k (these are the identifications made into
    edges in the projective embedding). This is non-bipartite for appropriate k.
    """
    G = nx.Graph()
    n = 2 * k
    for i in range(n):
        G.add_edge(i, (i + 1) % n)
    for i in range(k):
        G.add_edge(i, i + k)  # antipodal chords (Mobius-ladder = Mobius-Kantor-ish)
    return G


def cylinder_quadrangulation_rp2(a, b):
    """
    Quadrangulation of RP^2 as an (a x b) grid on a cylinder with the two
    boundary circles glued antipodally (cross-cap). Vertices (i,j), i in Z_a
    (around), j in 0..b (height). Top boundary (j=b) glued to itself antipodally:
    (i,b) ~ (i+a/2, b). This needs a even for the antipodal glue. Faces are quads.
    """
    G = nx.Graph()
    def V(i, j):
        return (i % a, j)
    for j in range(b + 1):
        for i in range(a):
            if j < b:
                G.add_edge(V(i, j), V(i, j + 1))  # vertical
            G.add_edge(V(i, j), V(i + 1, j))       # horizontal ring
    # antipodal glue at top: identify (i,b) with (i+a//2,b)
    if a % 2 == 0:
        for i in range(a // 2):
            G = nx.contracted_nodes(G, (i, b), ((i + a // 2) % a, b), self_loops=False)
    return nx.convert_node_labels_to_integers(G)


def profile(G, name, k=4):
    G = nx.convert_node_labels_to_integers(G)
    if G.number_of_nodes() < 4:
        print(f"[{name}] too small"); return None
    c3 = is_k_colorable(G, 3); c4 = is_k_colorable(G, 4)
    chi = 2 if is_k_colorable(G, 2) else (3 if c3 else (4 if c4 else ">=5"))
    line = f"[{name}] n={G.number_of_nodes()} m={G.number_of_edges()} chi={chi}"
    if chi != 4:
        print(line, flush=True); return None
    vc, _, bad = is_vertex_critical(G, 4)
    ce = critical_edges(G, 4)
    m = G.number_of_edges()
    print(f"{line} vertex_critical={vc} noncrit_v={len(bad)} "
          f"critical_edges={len(ce)} redundant={m-len(ce)} "
          f"({100*(m-len(ce))//m if m else 0}%)", flush=True)
    if vc and len(ce) == 0:
        edges = [tuple(sorted(e)) for e in G.edges()]
        if checkers.is_erdos944_k_r1(edges, G.number_of_nodes(), 4):
            print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
            return ("WITNESS", G)
    return (len(ce) if vc else None, G)


if __name__ == "__main__":
    print("=== Mobius-ladder-style antipodal quotients Q(k) ===", flush=True)
    for k in range(3, 12):
        profile(antipodal_quotient_prism(k), f"Q(k={k})")

    print("\n=== Cylinder quadrangulations of RP^2 (a even) ===", flush=True)
    for a in (4, 6, 8):
        for b in (1, 2, 3, 4):
            profile(cylinder_quadrangulation_rp2(a, b), f"cyl_rp2(a={a},b={b})")
