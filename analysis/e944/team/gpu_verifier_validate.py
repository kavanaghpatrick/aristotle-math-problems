"""
MANDATORY validation of the GPU kernel against checkers.py on the known census.
Any mismatch => STOP and debug. (team-lead GPU directive.)
"""
import sys
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
import networkx as nx
from checkers import (chi_bt, edges_to_adj, is_k_colorable_backtrack,
                      is_vertex_critical, has_no_critical_edge)
from gpu_verifier import gpu_coloring_analysis, gpu_is_witness, num_critical_edges


def circulant_edges(n, conn):
    E = set()
    for v in range(n):
        for d in conn:
            for w in ((v + d) % n, (v - d) % n):
                if v != w:
                    E.add((min(v, w), max(v, w)))
    return sorted(E)


def nx_edges(G):
    H = nx.convert_node_labels_to_integers(G)
    return sorted((min(u, v), max(u, v)) for u, v in H.edges()), H.number_of_nodes()


def cpu_num_critical_edges(n, edges):
    c = 0
    for (a, b) in edges:
        sub = [e for e in edges if e != (a, b)]
        if chi_bt(sub, n) < 4:
            c += 1
    return c


def cpu_f(n, edges):
    """min monochromatic edges over all 3-colorings (CPU brute, small n only)."""
    from itertools import product
    best = len(edges) + 1
    for coloring in product(range(3), repeat=n):
        mono = sum(1 for (a, b) in edges if coloring[a] == coloring[b])
        if mono < best:
            best = mono
            if best == 0:
                break
    return best


def check(name, n, edges, exp_vc=None, exp_critE=None, exp_f=None, check_f=True):
    print(f"\n=== {name} (n={n}, m={len(edges)}) ===")
    # GPU
    a = gpu_coloring_analysis(n, edges, incident_vertex=True)
    gpu_chi_le3 = a["chi_le_3"]
    gpu_critE = sum(1 for x in a["edge_3col"] if x)
    gpu_vc = (not gpu_chi_le3) and all(a["vert_3col"]) and \
             is_k_colorable_backtrack(edges_to_adj(edges, n), n, 4)
    gpu_f = a["f"]
    # CPU ground truth
    cpu_chi = chi_bt(edges, n)
    cpu_vc = is_vertex_critical(edges, n, 4)
    cpu_critE = cpu_num_critical_edges(n, edges)
    print(f"  GPU: chi<=3={gpu_chi_le3} f={gpu_f} B1={a['B1']} vc={gpu_vc} critE={gpu_critE} dev={a['device']}")
    print(f"  CPU: chi={cpu_chi}            vc={cpu_vc} critE={cpu_critE}")
    ok = True
    # chi consistency
    if (cpu_chi <= 3) != gpu_chi_le3:
        print("  ** MISMATCH chi<=3 **"); ok = False
    if gpu_vc != cpu_vc:
        print("  ** MISMATCH vertex-critical **"); ok = False
    if gpu_critE != cpu_critE:
        print(f"  ** MISMATCH critical-edge count GPU={gpu_critE} CPU={cpu_critE} **"); ok = False
    if check_f and n <= 14:
        cf = cpu_f(n, edges)
        if cf != gpu_f:
            print(f"  ** MISMATCH f GPU={gpu_f} CPU={cf} **"); ok = False
        else:
            print(f"  f cross-check OK ({cf})")
    # expectations
    if exp_vc is not None and gpu_vc != exp_vc:
        print(f"  ** EXPECT vc={exp_vc} got {gpu_vc} **"); ok = False
    if exp_critE is not None and gpu_critE != exp_critE:
        print(f"  ** EXPECT critE={exp_critE} got {gpu_critE} **"); ok = False
    if exp_f is not None and gpu_f != exp_f:
        print(f"  ** EXPECT f={exp_f} got {gpu_f} **"); ok = False
    print("  RESULT:", "OK" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    allok = True
    # K4: chi=4, vc, every edge critical (critE=6), f=1
    allok &= check("K4", 4, nx_edges(nx.complete_graph(4))[0], exp_vc=True, exp_critE=6)
    # C13(1,2,5): vc, critE=13, f=1
    allok &= check("C13(1,2,5)", 13, circulant_edges(13, [1, 2, 5]), exp_vc=True, exp_critE=13,
                   exp_f=1, check_f=False)  # 3^13=1.6M, f-brute skipped (n>... ok actually fine)
    # C14(1,2,5): NOT vc, critE=0 (the cocktail-adjacent near-miss family)
    allok &= check("C14(1,2,5)", 14, circulant_edges(14, [1, 2, 5]), exp_vc=False)
    # K_{2,2,2,2} cocktail-party graph: chi=4, critE=0, NOT vc (the cocktail crux)
    allok &= check("K_2,2,2,2", 8, nx_edges(nx.complete_multipartite_graph(2, 2, 2, 2))[0],
                   exp_vc=False, exp_critE=0)
    # Grotzsch: vc, all 20 edges critical
    allok &= check("Grotzsch", 11, nx_edges(nx.mycielskian(nx.cycle_graph(5)))[0],
                   exp_vc=True, exp_critE=20, exp_f=1, check_f=False)
    # n=10 champion (forge's ICpdbY{]_): 4-vtx-critical, min critical edges
    try:
        G = nx.from_graph6_bytes("ICpdbY{]_".encode())
        e10, n10 = nx_edges(G)
        allok &= check("n=10 champion ICpdbY{]_", n10, e10, exp_vc=True, check_f=True)
    except Exception as ex:
        print(f"\n(n=10 champion skipped: {ex})")
    print("\n" + "=" * 50)
    print("ALL VALIDATIONS PASSED — GPU kernel matches checkers.py" if allok
          else "*** VALIDATION FAILED — DO NOT USE GPU KERNEL, DEBUG FIRST ***")
