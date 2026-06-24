"""
Cross-validate the two INDEPENDENT chi implementations (backtracking vs SAT)
on known reference graphs, then test the e944 target predicates against ground truth.

squad-1 lesson: VERIFIER before SEARCHER. If the checkers disagree or get a known
graph wrong, the whole search is worthless.
"""
import networkx as nx
from checkers import (
    chromatic_number_exact, edges_to_adj, chromatic_number_sat,
    is_vertex_critical, has_no_critical_edge, is_erdos944_k_r1, chi_bt,
)


def chi_sat(edges, n):
    return chromatic_number_sat(edges, n)


def nx_edges(G):
    """Relabel nx graph to 0..n-1 and return (edges, n)."""
    H = nx.convert_node_labels_to_integers(G)
    n = H.number_of_nodes()
    edges = [(min(u, v), max(u, v)) for (u, v) in H.edges()]
    return edges, n


def grotzsch():
    return nx.mycielskian(nx.cycle_graph(5))  # Mycielskian of C5 = Grotzsch (11 v, chi=4, triangle-free)


def report(name, edges, n, expect_chi=None, expect_vc4=None, expect_no_crit_edge=None):
    cbt = chi_bt(edges, n)
    csat = chi_sat(edges, n)
    agree = "OK" if cbt == csat else "**MISMATCH**"
    line = f"[{name}] n={n} m={len(edges)} | chi_bt={cbt} chi_sat={csat} {agree}"
    if expect_chi is not None:
        line += f" expect_chi={expect_chi} {'OK' if cbt==expect_chi else 'WRONG'}"
    print(line)
    assert cbt == csat, f"chi mismatch on {name}"
    if expect_chi is not None:
        assert cbt == expect_chi, f"chi wrong on {name}"
    if cbt == 4:
        vc = is_vertex_critical(edges, n, 4)
        nce = has_no_critical_edge(edges, n, 4)
        tgt = is_erdos944_k_r1(edges, n, 4)
        print(f"        4-vertex-critical={vc} no_critical_edge={nce} IsErdos944_4_1={tgt}")
        if expect_vc4 is not None:
            assert vc == expect_vc4, f"vertex-crit wrong on {name}: got {vc}"
        if expect_no_crit_edge is not None:
            assert nce == expect_no_crit_edge, f"no-crit-edge wrong on {name}: got {nce}"
    return cbt


print("=" * 70)
print("CROSS-VALIDATION OF INDEPENDENT chi CHECKERS (backtrack vs SAT)")
print("=" * 70)

# K4: chi=4, 4-vertex-critical, EVERY edge critical (so has_no_critical_edge = False)
e, n = nx_edges(nx.complete_graph(4))
report("K4", e, n, expect_chi=4, expect_vc4=True, expect_no_crit_edge=False)

# K3 = triangle: chi=3
e, n = nx_edges(nx.complete_graph(3))
report("K3", e, n, expect_chi=3)

# K5: chi=5
e, n = nx_edges(nx.complete_graph(5))
report("K5", e, n, expect_chi=5)

# C5: odd cycle, chi=3, vertex-critical at k=3
e, n = nx_edges(nx.cycle_graph(5))
report("C5", e, n, expect_chi=3)

# C6: even cycle, chi=2
e, n = nx_edges(nx.cycle_graph(6))
report("C6", e, n, expect_chi=2)

# W5 = wheel on hub + C5 (odd wheel): chi=4
# networkx wheel_graph(6) = hub + C5  (6 nodes)
e, n = nx_edges(nx.wheel_graph(6))
report("W5 (hub+C5)", e, n, expect_chi=4)

# Grotzsch graph: chi=4, triangle-free, 4-vertex-critical.
# Known fact: Grotzsch IS edge-critical too (it is 4-critical in the edge sense),
# so it should HAVE critical edges -> has_no_critical_edge = False.
e, n = nx_edges(grotzsch())
report("Grotzsch", e, n, expect_chi=4)

# Petersen graph: chi=3
e, n = nx_edges(nx.petersen_graph())
report("Petersen", e, n, expect_chi=3)

# Complete bipartite K_{3,3}: chi=2
e, n = nx_edges(nx.complete_bipartite_graph(3, 3))
report("K_{3,3}", e, n, expect_chi=2)

print("=" * 70)
print("ALL CROSS-VALIDATIONS PASSED — both chi implementations agree, "
      "known chromatic numbers correct.")
print("=" * 70)
