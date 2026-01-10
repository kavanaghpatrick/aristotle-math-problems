#!/usr/bin/env python3
"""
Counterexample Search for Tuza's Conjecture with nu=4

Goal: Find a graph G where:
  - nu(G) = 4 (maximum edge-disjoint triangle packing has exactly 4 triangles)
  - tau(G) >= 9 (minimum edge cover needs at least 9 edges)

If such a graph exists, Tuza's conjecture (tau <= 2*nu) would be FALSE for nu=4.

Strategy:
1. Build cycle_4 configurations (the hardest case)
2. Add external triangles strategically to maximize tau while keeping nu=4
3. Check if tau >= 9 is achievable
"""

import itertools
from collections import defaultdict
from typing import Set, Tuple, List, FrozenSet

def triangles_in_graph(edges: Set[Tuple[int, int]]) -> Set[FrozenSet[int]]:
    """Find all triangles in the graph."""
    adj = defaultdict(set)
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)

    vertices = set()
    for u, v in edges:
        vertices.add(u)
        vertices.add(v)

    triangles = set()
    for v in vertices:
        neighbors = list(adj[v])
        for i in range(len(neighbors)):
            for j in range(i + 1, len(neighbors)):
                u, w = neighbors[i], neighbors[j]
                if w in adj[u]:
                    triangles.add(frozenset([u, v, w]))
    return triangles

def triangle_edges(t: FrozenSet[int]) -> Set[Tuple[int, int]]:
    """Get the 3 edges of a triangle."""
    verts = list(t)
    return {
        (min(verts[0], verts[1]), max(verts[0], verts[1])),
        (min(verts[0], verts[2]), max(verts[0], verts[2])),
        (min(verts[1], verts[2]), max(verts[1], verts[2])),
    }

def triangles_edge_disjoint(t1: FrozenSet[int], t2: FrozenSet[int]) -> bool:
    """Check if two triangles share no edges."""
    return len(triangle_edges(t1) & triangle_edges(t2)) == 0

def compute_nu(triangles: Set[FrozenSet[int]]) -> Tuple[int, List[FrozenSet[int]]]:
    """Compute nu (max edge-disjoint triangle packing) via greedy + backtracking."""
    tri_list = list(triangles)
    n = len(tri_list)

    best_packing = []

    def backtrack(idx: int, current: List[int], used_edges: Set[Tuple[int, int]]):
        nonlocal best_packing

        if len(current) > len(best_packing):
            best_packing = [tri_list[i] for i in current]

        # Pruning: can we possibly beat the best?
        remaining = n - idx
        if len(current) + remaining <= len(best_packing):
            return

        for i in range(idx, n):
            t = tri_list[i]
            t_edges = triangle_edges(t)
            if not (t_edges & used_edges):
                backtrack(i + 1, current + [i], used_edges | t_edges)

    backtrack(0, [], set())
    return len(best_packing), best_packing

def compute_tau(graph_edges: Set[Tuple[int, int]], triangles: Set[FrozenSet[int]]) -> int:
    """Compute tau (minimum edge cover) via brute force for small instances."""
    if not triangles:
        return 0

    edge_list = list(graph_edges)
    n = len(edge_list)

    # Check increasing cover sizes
    for k in range(1, n + 1):
        for cover in itertools.combinations(range(n), k):
            cover_edges = {edge_list[i] for i in cover}
            # Check if this cover hits all triangles
            covers_all = True
            for t in triangles:
                t_edges = triangle_edges(t)
                if not (t_edges & cover_edges):
                    covers_all = False
                    break
            if covers_all:
                return k

    return n  # Worst case: need all edges

def compute_tau_ilp(graph_edges: Set[Tuple[int, int]], triangles: Set[FrozenSet[int]]) -> int:
    """Compute tau using ILP for larger instances."""
    try:
        from scipy.optimize import milp, LinearConstraint, Bounds
        import numpy as np
    except ImportError:
        return compute_tau(graph_edges, triangles)

    if not triangles:
        return 0

    edge_list = list(graph_edges)
    n = len(edge_list)
    edge_to_idx = {e: i for i, e in enumerate(edge_list)}

    # Objective: minimize sum of x_e
    c = np.ones(n)

    # Constraints: for each triangle, at least one edge must be covered
    A = []
    for t in triangles:
        row = np.zeros(n)
        for e in triangle_edges(t):
            if e in edge_to_idx:
                row[edge_to_idx[e]] = 1
        A.append(row)

    A = np.array(A)
    b_l = np.ones(len(triangles))  # >= 1
    b_u = np.full(len(triangles), np.inf)  # no upper bound

    constraints = LinearConstraint(A, b_l, b_u)
    bounds = Bounds(0, 1)  # 0 <= x <= 1 (integrality will be enforced)
    integrality = np.ones(n)  # all variables are integers

    result = milp(c, constraints=constraints, bounds=bounds, integrality=integrality)

    if result.success:
        return int(round(result.fun))
    else:
        return compute_tau(graph_edges, triangles)

def build_cycle4_graph(add_externals: List[Tuple[int, int, int]] = None):
    """
    Build a cycle_4 configuration.

    M = {A, B, C, D} where:
    - A = {0, 1, 2}, B = {2, 3, 4}, C = {4, 5, 6}, D = {6, 7, 0}
    - Shared vertices: v_ab=2, v_bc=4, v_cd=6, v_da=0

    Returns edges, M-triangles
    """
    # M-triangles
    A = frozenset([0, 1, 2])
    B = frozenset([2, 3, 4])
    C = frozenset([4, 5, 6])
    D = frozenset([6, 7, 0])

    M = [A, B, C, D]

    # Build edges from M
    edges = set()
    for t in M:
        edges |= triangle_edges(t)

    # Add external triangles
    if add_externals:
        for ext in add_externals:
            t = frozenset(ext)
            ext_edges = triangle_edges(t)
            edges |= ext_edges

    return edges, M

def find_counterexample():
    """
    Systematically search for counterexamples.

    Strategy: Start with cycle_4 and add external triangles
    that maximize tau while keeping nu=4.
    """

    print("=" * 60)
    print("COUNTEREXAMPLE SEARCH FOR TUZA'S CONJECTURE (nu=4)")
    print("=" * 60)

    # Base cycle_4
    base_edges, M = build_cycle4_graph()

    print("\nBase cycle_4 configuration:")
    print(f"  M-triangles: {[set(t) for t in M]}")
    print(f"  Edges: {len(base_edges)}")

    base_triangles = triangles_in_graph(base_edges)
    nu, packing = compute_nu(base_triangles)
    tau = compute_tau(base_edges, base_triangles)

    print(f"  Triangles: {len(base_triangles)}")
    print(f"  nu = {nu}, tau = {tau}")
    print(f"  Tuza bound: 2*nu = {2*nu}")
    print(f"  Gap: tau - 2*nu = {tau - 2*nu}")

    # Now try adding external triangles
    # Vertices: 0-7 are base, 8+ are external

    print("\n" + "=" * 60)
    print("SEARCHING FOR EXTERNAL TRIANGLES THAT INCREASE TAU")
    print("=" * 60)

    # External triangles must share an edge with M (by maximality)
    # Try triangles at each shared vertex
    shared_vertices = [0, 2, 4, 6]  # v_da, v_ab, v_bc, v_cd

    # Generate candidate external triangles
    # At v_ab=2: can add triangles using edges from A or B
    # A = {0,1,2}, B = {2,3,4}
    # External at v_ab could be: {0,2,x}, {1,2,x}, {2,3,x}, {2,4,x}

    external_candidates = []
    next_vertex = 8

    # At v_ab = 2 (A={0,1,2}, B={2,3,4})
    for base_v in [0, 1]:  # from A
        external_candidates.append((base_v, 2, next_vertex))
        next_vertex += 1
    for base_v in [3, 4]:  # from B
        external_candidates.append((2, base_v, next_vertex))
        next_vertex += 1

    # At v_bc = 4 (B={2,3,4}, C={4,5,6})
    for base_v in [2, 3]:  # from B
        external_candidates.append((base_v, 4, next_vertex))
        next_vertex += 1
    for base_v in [5, 6]:  # from C
        external_candidates.append((4, base_v, next_vertex))
        next_vertex += 1

    # At v_cd = 6 (C={4,5,6}, D={6,7,0})
    for base_v in [4, 5]:  # from C
        external_candidates.append((base_v, 6, next_vertex))
        next_vertex += 1
    for base_v in [7, 0]:  # from D
        external_candidates.append((6, base_v, next_vertex))
        next_vertex += 1

    # At v_da = 0 (D={6,7,0}, A={0,1,2})
    for base_v in [6, 7]:  # from D
        external_candidates.append((base_v, 0, next_vertex))
        next_vertex += 1
    for base_v in [1, 2]:  # from A
        external_candidates.append((0, base_v, next_vertex))
        next_vertex += 1

    print(f"\nGenerated {len(external_candidates)} external triangle candidates")

    # Test adding combinations of externals
    best_tau = tau
    best_config = None

    # Try adding 1 external at a time first
    print("\nTrying single externals...")
    for ext in external_candidates:
        edges, _ = build_cycle4_graph([ext])
        triangles = triangles_in_graph(edges)
        nu_test, _ = compute_nu(triangles)

        if nu_test == 4:  # Keep nu=4
            tau_test = compute_tau(edges, triangles)
            if tau_test > best_tau:
                best_tau = tau_test
                best_config = [ext]
                print(f"  External {ext}: nu={nu_test}, tau={tau_test} (NEW BEST!)")

    # Try pairs
    print("\nTrying pairs of externals...")
    for i, ext1 in enumerate(external_candidates):
        for ext2 in external_candidates[i+1:]:
            edges, _ = build_cycle4_graph([ext1, ext2])
            triangles = triangles_in_graph(edges)
            nu_test, _ = compute_nu(triangles)

            if nu_test == 4:
                tau_test = compute_tau(edges, triangles)
                if tau_test > best_tau:
                    best_tau = tau_test
                    best_config = [ext1, ext2]
                    print(f"  Externals {ext1}, {ext2}: nu={nu_test}, tau={tau_test} (NEW BEST!)")

    # Try triples
    print("\nTrying triples of externals...")
    count = 0
    for i, ext1 in enumerate(external_candidates):
        for j, ext2 in enumerate(external_candidates[i+1:], i+1):
            for ext3 in external_candidates[j+1:]:
                edges, _ = build_cycle4_graph([ext1, ext2, ext3])
                triangles = triangles_in_graph(edges)
                nu_test, _ = compute_nu(triangles)

                if nu_test == 4:
                    tau_test = compute_tau(edges, triangles)
                    if tau_test > best_tau:
                        best_tau = tau_test
                        best_config = [ext1, ext2, ext3]
                        print(f"  Externals {ext1}, {ext2}, {ext3}: nu={nu_test}, tau={tau_test} (NEW BEST!)")
                count += 1
    print(f"  Tested {count} triples")

    # Try 4-tuples (this might be slow)
    print("\nTrying 4-tuples of externals (may be slow)...")
    count = 0
    for combo in itertools.combinations(external_candidates, 4):
        edges, _ = build_cycle4_graph(list(combo))
        triangles = triangles_in_graph(edges)
        nu_test, _ = compute_nu(triangles)

        if nu_test == 4:
            tau_test = compute_tau(edges, triangles)
            if tau_test > best_tau:
                best_tau = tau_test
                best_config = list(combo)
                print(f"  4 externals: nu={nu_test}, tau={tau_test} (NEW BEST!)")
        count += 1
        if count % 1000 == 0:
            print(f"  ... tested {count} 4-tuples")

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"\nBest configuration found:")
    print(f"  tau = {best_tau}")
    print(f"  nu = 4")
    print(f"  Tuza bound: 2*nu = 8")

    if best_tau >= 9:
        print("\n*** COUNTEREXAMPLE FOUND! ***")
        print(f"Graph with nu=4 but tau={best_tau} >= 9")
        print(f"This would DISPROVE Tuza's conjecture!")
    else:
        print(f"\n  Gap: tau - 2*nu = {best_tau - 8}")
        print("  No counterexample found in this search space.")
        print("  Tuza's conjecture HOLDS for tested configurations.")

    return best_tau, best_config

def analyze_tau_gap():
    """
    Analyze why tau <= 8 might always hold.

    Key insight: In cycle_4, each external triangle shares an M-edge.
    Cover strategy: For each shared vertex v, use edges that cover:
      1. The two M-triangles meeting at v
      2. All externals using M-edges at v
    """

    print("\n" + "=" * 60)
    print("ANALYSIS: WHY TAU <= 8 MIGHT HOLD")
    print("=" * 60)

    # Build a "worst case" cycle_4 with many externals
    edges, M = build_cycle4_graph()

    # Add externals at each shared vertex
    externals = []
    next_v = 8

    # At v_ab=2: add 4 externals using all 4 M-edges at vertex 2
    # A = {0,1,2} has edges {0,2}, {1,2}, {0,1}
    # B = {2,3,4} has edges {2,3}, {2,4}, {3,4}
    # M-edges at 2: {0,2}, {1,2}, {2,3}, {2,4}
    externals.extend([
        (0, 2, next_v), (1, 2, next_v+1),  # using A-edges
        (2, 3, next_v+2), (2, 4, next_v+3)  # using B-edges
    ])
    next_v += 4

    # At v_bc=4: add 4 externals
    externals.extend([
        (2, 4, next_v), (3, 4, next_v+1),  # using B-edges
        (4, 5, next_v+2), (4, 6, next_v+3)  # using C-edges
    ])
    next_v += 4

    # At v_cd=6: add 4 externals
    externals.extend([
        (4, 6, next_v), (5, 6, next_v+1),  # using C-edges
        (6, 7, next_v+2), (6, 0, next_v+3)  # using D-edges
    ])
    next_v += 4

    # At v_da=0: add 4 externals
    externals.extend([
        (6, 0, next_v), (7, 0, next_v+1),  # using D-edges
        (0, 1, next_v+2), (0, 2, next_v+3)  # using A-edges
    ])
    next_v += 4

    edges, _ = build_cycle4_graph(externals)
    triangles = triangles_in_graph(edges)

    print(f"\nWorst-case cycle_4 with {len(externals)} external candidates:")
    print(f"  Total triangles: {len(triangles)}")

    nu, packing = compute_nu(triangles)
    print(f"  nu = {nu}")

    if nu != 4:
        print(f"  Note: nu != 4, so this isn't a valid test case")
        return

    tau = compute_tau_ilp(edges, triangles)
    print(f"  tau = {tau}")
    print(f"  Tuza bound: 2*nu = 8")

    if tau <= 8:
        print("\n  OBSERVATION: Even with many externals, tau <= 8!")
        print("  This suggests a structural reason tau is bounded.")

        # Try to find the optimal cover
        print("\n  Searching for 8-edge cover...")
        edge_list = list(edges)
        found_8_cover = False
        for cover_edges in itertools.combinations(edge_list, 8):
            cover_set = set(cover_edges)
            covers_all = all(
                triangle_edges(t) & cover_set
                for t in triangles
            )
            if covers_all:
                print(f"  Found 8-edge cover: {cover_set}")
                found_8_cover = True
                break

        if not found_8_cover:
            print("  No 8-edge cover found (tau > 8)")
    else:
        print(f"\n  *** POTENTIAL COUNTEREXAMPLE: tau = {tau} > 8 ***")

if __name__ == "__main__":
    find_counterexample()
    analyze_tau_gap()
