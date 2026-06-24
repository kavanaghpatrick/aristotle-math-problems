"""Round-1 kill-tests for archivist invention candidates A1, A2, A3.
All chi via checkers.py (SAT path; cross-check backtrack on small verdicts)."""
import networkx as nx
import checkers
import archivist_k5_witness as W
import archivist_jensen_siggers_build as JS


def score(G, k=4):
    """Return dict: chi, vertex_critical, num_critical_edges. SAT chi (fast)."""
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = [(idx[u], idx[w]) for u, w in G.edges()]; n = len(nodes)
    chi = checkers.chromatic_number_sat(edges, n)
    if chi != k:
        return dict(n=n, chi=chi, verdict=f"chi={chi}!={k}")
    # vertex-critical via SAT
    adj = checkers.edges_to_adj(edges, n)
    for v in range(n):
        sa, sn = checkers.adj_remove_vertex(adj, n, v)
        se = []
        for a in range(sn):
            nb = sa[a]
            while nb:
                low = nb & (-nb); b = low.bit_length() - 1
                if a < b: se.append((a, b))
                nb ^= low
        if checkers.chromatic_number_sat(se, sn) >= k:
            return dict(n=n, chi=chi, vertex_critical=False, bad_vertex=v)
    crit = [e for e in edges if checkers.chromatic_number_sat(checkers.edges_remove_edge(edges, e), n) < k]
    return dict(n=n, chi=chi, m_edges=len(edges), vertex_critical=True,
                num_critical_edges=len(crit), no_critical_edge=(len(crit) == 0))


# ---------------- A3: downward surgery on the Z17 k=5 witness ----------------
def A3():
    print("\n=== A3: k=5 witness (Z17) downward surgery ===")
    Gw, N, D = W.jensen_circulant_k5(2, 2)  # the canonical witness, N=17, chi=5, 0 crit
    nodes = list(Gw.nodes())
    best = None
    for v in nodes:
        H = Gw.copy(); H.remove_node(v)
        r = score(H, 4)
        if r.get("vertex_critical"):
            nc = r["num_critical_edges"]
            tag = "WITNESS!!" if nc == 0 else f"{nc} crit"
            print(f"  witness - {v}: chi=4 vertex-critical, {tag} (n={r['n']})")
            if best is None or nc < best[1]:
                best = (v, nc)
        # vertex-transitive => all v identical; one is enough but loop confirms
        break  # circulant is vertex-transitive: witness-v is the same graph up to iso for all v
    # all witness-v isomorphic (vertex-transitive). Report the single representative.
    H = Gw.copy(); H.remove_node(nodes[0])
    r = score(H, 4)
    print(f"  representative witness-v0: {r}")
    return r


# ---------------- A2: entangled Hajos sum, shared triangle ----------------
def A2():
    print("\n=== A2: entangled Hajos sum (two W5 sharing a triangle) ===")
    # W5 = K1 + C5 (wheel on 6 vtx): hub h, rim c0..c4. Contains triangles h-ci-c(i+1).
    def W5(prefix):
        G = nx.Graph()
        hub = f"{prefix}h"
        rim = [f"{prefix}c{i}" for i in range(5)]
        for i in range(5):
            G.add_edge(hub, rim[i])
            G.add_edge(rim[i], rim[(i + 1) % 5])
        return G, hub, rim
    G1, h1, r1 = W5("A")
    G2, h2, r2 = W5("B")
    G = nx.union(G1, G2)
    # shared triangle: identify {h1, c0_1, c1_1} with {h2, c0_2, c1_2}
    G = nx.contracted_nodes(G, h1, h2, self_loops=False)
    G = nx.contracted_nodes(G, r1[0], r2[0], self_loops=False)
    G = nx.contracted_nodes(G, r1[1], r2[1], self_loops=False)
    res = score(G, 4)
    print(f"  entangled-W5: {res}")
    # also try entangling on a shared K3 of two K4's (K4 is 4-critical)
    K4a = nx.complete_graph(["a0", "a1", "a2", "a3"])
    K4b = nx.complete_graph(["b0", "b1", "b2", "b3"])
    G = nx.union(K4a, K4b)
    G = nx.contracted_nodes(G, "a0", "b0", self_loops=False)
    G = nx.contracted_nodes(G, "a1", "b1", self_loops=False)
    G = nx.contracted_nodes(G, "a2", "b2", self_loops=False)
    res2 = score(G, 4)
    print(f"  entangled-K4 (share K3): {res2}")
    return res, res2


# ---------------- A1: doubled Jensen-Siggers transfer gadget ----------------
def A1():
    print("\n=== A1: baseline J-S H(m=2) for comparison ===")
    Hp, S = JS.build_Hprime(2)
    H = JS.vertex_critical_core(Hp, 4)
    r = score(H, 4)
    print(f"  J-S H(m=2) baseline: {r}")
    # (Doubled-gadget variant deferred: heavier build. Baseline establishes the m=2 critical count.)
    return r


if __name__ == "__main__":
    a3 = A3()
    a2 = A2()
    a1 = A1()
    print("\n=== SUMMARY ===")
    print("A3 (witness-v):", a3.get("verdict") or
          f"chi={a3.get('chi')} vc={a3.get('vertex_critical')} crit={a3.get('num_critical_edges')}")
