#!/usr/bin/env python3
"""
Counterexample Search v2 for Tuza's Conjecture with nu=4

Key insight from v1: Adding arbitrary externals increases nu.
The challenge: Add externals that are "forced" to share edges with M,
so they can't form additional independent triangles.

Strategy:
1. Externals must share an M-edge (by maximality)
2. For nu to stay 4, externals must pairwise share edges among themselves
   (otherwise we could pick an external instead of an M-triangle)
3. Focus on "sunflower" configurations where externals share a common vertex
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

def compute_nu(triangles: Set[FrozenSet[int]]) -> Tuple[int, List[FrozenSet[int]]]:
    """Compute nu (max edge-disjoint triangle packing) via backtracking."""
    tri_list = list(triangles)
    n = len(tri_list)

    best_packing = []

    def backtrack(idx: int, current: List[int], used_edges: Set[Tuple[int, int]]):
        nonlocal best_packing

        if len(current) > len(best_packing):
            best_packing = [tri_list[i] for i in current]

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
    """Compute tau (minimum edge cover) via brute force."""
    if not triangles:
        return 0

    edge_list = list(graph_edges)
    n = len(edge_list)

    for k in range(1, n + 1):
        for cover in itertools.combinations(range(n), k):
            cover_edges = {edge_list[i] for i in cover}
            if all(triangle_edges(t) & cover_edges for t in triangles):
                return k

    return n

def build_sunflower_at_vertex(base_vertex: int, m_edges: List[Tuple[int, int]], apex: int) -> List[FrozenSet[int]]:
    """
    Build a sunflower of externals at base_vertex with common apex.

    All externals share edge {base_vertex, apex}, so they pairwise share an edge.
    This prevents externals from forming an independent packing.
    """
    externals = []
    for e in m_edges:
        # e is an M-edge incident to base_vertex
        other_v = e[0] if e[1] == base_vertex else e[1]
        # External: {base_vertex, other_v, apex}
        ext = frozenset([base_vertex, other_v, apex])
        externals.append(ext)
    return externals

def analyze_cycle4_with_sunflowers():
    """
    Build cycle_4 with sunflower externals at each shared vertex.

    M = {A, B, C, D}:
    - A = {0, 1, 2}, B = {2, 3, 4}, C = {4, 5, 6}, D = {6, 7, 0}
    - v_ab=2, v_bc=4, v_cd=6, v_da=0
    """

    print("=" * 60)
    print("CYCLE_4 WITH SUNFLOWER EXTERNALS")
    print("=" * 60)

    # M-triangles
    A = frozenset([0, 1, 2])
    B = frozenset([2, 3, 4])
    C = frozenset([4, 5, 6])
    D = frozenset([6, 7, 0])
    M = [A, B, C, D]

    # Build base edges
    edges = set()
    for t in M:
        edges |= triangle_edges(t)

    print("\nBase cycle_4:")
    print(f"  M = {[set(t) for t in M]}")
    print(f"  Edges: {len(edges)}")

    # Add sunflowers at each shared vertex
    # v_ab = 2: M-edges are {0,2}, {1,2} from A and {2,3}, {2,4} from B
    # v_bc = 4: M-edges are {2,4}, {3,4} from B and {4,5}, {4,6} from C
    # v_cd = 6: M-edges are {4,6}, {5,6} from C and {6,7}, {0,6} from D
    # v_da = 0: M-edges are {6,0}, {7,0} from D and {0,1}, {0,2} from A

    # For sunflower, all externals at v share a common apex
    # This ensures externals pairwise share the edge {v, apex}

    # Apex vertices: 8, 9, 10, 11 (one per shared vertex)
    apex_ab, apex_bc, apex_cd, apex_da = 8, 9, 10, 11

    # Sunflower at v_ab = 2
    sunflower_ab = [
        frozenset([0, 2, apex_ab]),  # using {0,2}
        frozenset([1, 2, apex_ab]),  # using {1,2}
        frozenset([2, 3, apex_ab]),  # using {2,3}
        frozenset([2, 4, apex_ab]),  # using {2,4}
    ]

    # Sunflower at v_bc = 4
    sunflower_bc = [
        frozenset([2, 4, apex_bc]),  # using {2,4}
        frozenset([3, 4, apex_bc]),  # using {3,4}
        frozenset([4, 5, apex_bc]),  # using {4,5}
        frozenset([4, 6, apex_bc]),  # using {4,6}
    ]

    # Sunflower at v_cd = 6
    sunflower_cd = [
        frozenset([4, 6, apex_cd]),  # using {4,6}
        frozenset([5, 6, apex_cd]),  # using {5,6}
        frozenset([6, 7, apex_cd]),  # using {6,7}
        frozenset([0, 6, apex_cd]),  # using {0,6}
    ]

    # Sunflower at v_da = 0
    sunflower_da = [
        frozenset([6, 0, apex_da]),  # using {6,0}
        frozenset([7, 0, apex_da]),  # using {7,0}
        frozenset([0, 1, apex_da]),  # using {0,1}
        frozenset([0, 2, apex_da]),  # using {0,2}
    ]

    all_externals = sunflower_ab + sunflower_bc + sunflower_cd + sunflower_da

    # Add edges for all externals
    for ext in all_externals:
        edges |= triangle_edges(ext)

    triangles = triangles_in_graph(edges)

    print(f"\nWith sunflower externals:")
    print(f"  Total edges: {len(edges)}")
    print(f"  Total triangles: {len(triangles)}")
    print(f"  Externals added: {len(all_externals)}")

    nu, packing = compute_nu(triangles)
    print(f"\n  nu = {nu}")
    print(f"  Packing: {[set(t) for t in packing]}")

    if nu > 4:
        print(f"\n  Note: nu = {nu} > 4")
        print("  Externals aren't forced to share enough edges!")

        # Analyze why nu increased
        # Check which externals are in the packing
        ext_set = set(all_externals)
        packing_externals = [t for t in packing if t in ext_set]
        packing_M = [t for t in packing if t in M]
        print(f"\n  Packing contains {len(packing_M)} M-triangles and {len(packing_externals)} externals")
        print(f"  M in packing: {[set(t) for t in packing_M]}")
        print(f"  Externals in packing: {[set(t) for t in packing_externals]}")

    else:
        tau = compute_tau(edges, triangles)
        print(f"  tau = {tau}")
        print(f"  Tuza bound: 2*nu = {2*nu}")

        if tau >= 9:
            print("\n  *** COUNTEREXAMPLE FOUND! ***")
        else:
            print(f"  tau <= 8: Tuza's conjecture HOLDS")

def analyze_forced_externals():
    """
    Key insight: For nu to stay 4, externals must share edges
    not just with M, but also with EACH OTHER.

    The "5-packing contradiction" (slot180):
    If we have 5 edge-disjoint triangles, one can replace an M-triangle.

    So externals must form a "clique" in the edge-sharing graph.
    """

    print("\n" + "=" * 60)
    print("ANALYZING FORCED EXTERNAL STRUCTURE")
    print("=" * 60)

    print("""
For nu to remain 4, we need:
1. Every external shares an M-edge (maximality)
2. Any subset of externals that are pairwise edge-disjoint
   has size ≤ 0 (otherwise we could form a 5-packing)

This means: ANY two externals must share an edge!

At shared vertex v with apex x:
- All externals have form {v, m_i, x} where m_i is the other vertex of M-edge
- Any two externals {v, m_i, x} and {v, m_j, x} share edge {v, x}
- This satisfies condition 2!

But what about externals at DIFFERENT shared vertices?
- External at v_ab: {2, m, 8}
- External at v_bc: {4, n, 9}
- Do these share an edge? Only if 8=9 or if {2,m} = {4,n} etc.

KEY INSIGHT: Externals at different shared vertices might NOT share edges!
If they're edge-disjoint, we could form a larger packing.

Let's check...
""")

    # Test: external at v_ab vs external at v_bc
    ext_ab = frozenset([0, 2, 8])  # uses {0,2} from A
    ext_bc = frozenset([5, 4, 9])  # uses {4,5} from C

    edges_ab = triangle_edges(ext_ab)
    edges_bc = triangle_edges(ext_bc)

    print(f"External at v_ab: {set(ext_ab)}, edges: {edges_ab}")
    print(f"External at v_bc: {set(ext_bc)}, edges: {edges_bc}")
    print(f"Shared edges: {edges_ab & edges_bc}")

    if not (edges_ab & edges_bc):
        print("\nThese externals are EDGE-DISJOINT!")
        print("This means we could potentially form a 5-packing:")
        print("  M - {A} + {ext_ab} + {ext_bc} if ext_ab edge-disjoint from B,C,D")

def search_constrained_externals():
    """
    Search for externals that are forced to share edges with each other.

    Key constraint: All externals must pairwise share at least one edge.
    This is extremely restrictive!
    """

    print("\n" + "=" * 60)
    print("SEARCHING FOR CONSTRAINED EXTERNAL CONFIGURATIONS")
    print("=" * 60)

    # M-triangles
    A = frozenset([0, 1, 2])
    B = frozenset([2, 3, 4])
    C = frozenset([4, 5, 6])
    D = frozenset([6, 7, 0])
    M = [A, B, C, D]

    # All M-edges
    M_edges = set()
    for t in M:
        M_edges |= triangle_edges(t)

    print(f"M-edges: {M_edges}")

    # For each subset of M-edges, check if we can add externals
    # that pairwise share edges

    # Try: use a SINGLE apex for all externals
    # All externals have form {v, w, apex} where {v,w} is an M-edge
    # Two externals {v1,w1,apex} and {v2,w2,apex} share edge iff
    # they share a vertex other than apex (since both include apex)

    apex = 8

    # Generate all possible externals with this apex
    possible_externals = []
    for e in M_edges:
        v, w = e
        ext = frozenset([v, w, apex])
        possible_externals.append(ext)

    print(f"\nWith single apex {apex}, possible externals: {len(possible_externals)}")

    # Check pairwise edge-sharing
    def pairwise_share_edges(externals: List[FrozenSet[int]]) -> bool:
        for i in range(len(externals)):
            for j in range(i + 1, len(externals)):
                e1 = triangle_edges(externals[i])
                e2 = triangle_edges(externals[j])
                if not (e1 & e2):
                    return False
        return True

    # Find maximal sets of externals that pairwise share edges
    print("\nSearching for maximal pairwise edge-sharing sets...")

    best_set = []
    for size in range(len(possible_externals), 0, -1):
        for combo in itertools.combinations(possible_externals, size):
            if pairwise_share_edges(list(combo)):
                best_set = list(combo)
                print(f"  Found set of size {size}: {[set(t) for t in best_set]}")
                break
        if best_set:
            break

    if best_set:
        # Build graph with M + best externals
        edges = set()
        for t in M:
            edges |= triangle_edges(t)
        for ext in best_set:
            edges |= triangle_edges(ext)

        triangles = triangles_in_graph(edges)
        nu, packing = compute_nu(triangles)
        tau = compute_tau(edges, triangles)

        print(f"\nResulting graph:")
        print(f"  nu = {nu}, tau = {tau}")
        print(f"  Tuza bound: 2*nu = {2*nu}")

        if nu == 4 and tau >= 9:
            print("\n  *** COUNTEREXAMPLE FOUND! ***")
        elif nu > 4:
            print(f"  nu = {nu} > 4, not a valid configuration")
        else:
            print(f"  Tuza's conjecture holds: tau = {tau} <= {2*nu}")

def search_with_two_apexes():
    """
    Try using two apex vertices - one for each "pair" of shared vertices.
    """
    print("\n" + "=" * 60)
    print("SEARCHING WITH TWO APEX VERTICES")
    print("=" * 60)

    # M-triangles
    A = frozenset([0, 1, 2])
    B = frozenset([2, 3, 4])
    C = frozenset([4, 5, 6])
    D = frozenset([6, 7, 0])
    M = [A, B, C, D]

    # Try: apex1 = 8 for edges at v_ab=2 and v_cd=6 (opposite)
    #      apex2 = 9 for edges at v_bc=4 and v_da=0 (opposite)

    apex1, apex2 = 8, 9

    # M-edges at v_ab=2: {0,2}, {1,2}, {2,3}, {2,4}
    # M-edges at v_cd=6: {4,6}, {5,6}, {6,7}, {0,6}
    edges_at_2_and_6 = [(0,2), (1,2), (2,3), (2,4), (4,6), (5,6), (6,7), (0,6)]

    # M-edges at v_bc=4: {2,4}, {3,4}, {4,5}, {4,6}
    # M-edges at v_da=0: {6,0}, {7,0}, (0,1), {0,2}
    edges_at_4_and_0 = [(2,4), (3,4), (4,5), (4,6), (6,0), (7,0), (0,1), (0,2)]

    # Generate externals
    externals_apex1 = [frozenset([e[0], e[1], apex1]) for e in edges_at_2_and_6]
    externals_apex2 = [frozenset([e[0], e[1], apex2]) for e in edges_at_4_and_0]

    print(f"Externals with apex1={apex1}: {len(externals_apex1)}")
    print(f"Externals with apex2={apex2}: {len(externals_apex2)}")

    # Key question: Do externals from different apex groups share edges?
    # {v, w, apex1} and {x, y, apex2} share edge iff {v,w} = {x,y} or they share a vertex pair

    # Check cross-group edge sharing
    print("\nChecking cross-group edge sharing...")
    cross_share_count = 0
    cross_disjoint_count = 0
    for ext1 in externals_apex1:
        for ext2 in externals_apex2:
            e1 = triangle_edges(ext1)
            e2 = triangle_edges(ext2)
            if e1 & e2:
                cross_share_count += 1
            else:
                cross_disjoint_count += 1
                if cross_disjoint_count <= 5:
                    print(f"  DISJOINT: {set(ext1)} and {set(ext2)}")

    print(f"\nCross-group pairs: {cross_share_count} share edges, {cross_disjoint_count} are disjoint")

    if cross_disjoint_count > 0:
        print("\nSome externals from different groups are edge-disjoint!")
        print("This allows forming larger packings, increasing nu beyond 4.")

def find_extreme_configuration():
    """
    Try to maximize tau/nu ratio through careful construction.
    """
    print("\n" + "=" * 60)
    print("SEARCHING FOR EXTREME TAU/NU CONFIGURATIONS")
    print("=" * 60)

    # Strategy: Build a graph where triangles are highly "interlocked"
    # so many edges are needed to hit them all

    # The "Fan" construction:
    # 4 M-triangles share a common vertex (star_all_4 case)
    # This is already proven to have tau <= 8

    # Try: Maximize triangle count while keeping nu = 4
    # by using a single "super-apex" connected to all M-vertices

    print("\nAttempting 'super-apex' construction...")

    # M-triangles all share vertex 0
    # A = {0, 1, 2}, B = {0, 3, 4}, C = {0, 5, 6}, D = {0, 7, 8}
    A = frozenset([0, 1, 2])
    B = frozenset([0, 3, 4])
    C = frozenset([0, 5, 6])
    D = frozenset([0, 7, 8])
    M = [A, B, C, D]

    edges = set()
    for t in M:
        edges |= triangle_edges(t)

    # Add a super-apex 9 connected to all M-vertices except 0
    super_apex = 9
    for v in [1, 2, 3, 4, 5, 6, 7, 8]:
        edges.add((min(v, super_apex), max(v, super_apex)))

    # This creates many triangles through super_apex
    triangles = triangles_in_graph(edges)

    print(f"Super-apex graph:")
    print(f"  M = {[set(t) for t in M]}")
    print(f"  Total edges: {len(edges)}")
    print(f"  Total triangles: {len(triangles)}")

    nu, packing = compute_nu(triangles)
    print(f"  nu = {nu}")

    if nu == 4:
        tau = compute_tau(edges, triangles)
        print(f"  tau = {tau}")
        print(f"  Ratio tau/nu = {tau/nu:.2f}")
        print(f"  Tuza bound: tau <= 2*nu = {2*nu}")

        if tau > 8:
            print("\n  *** COUNTEREXAMPLE! ***")
    else:
        print(f"  nu = {nu} != 4, not a valid test")

def exhaustive_small_search():
    """
    Exhaustively search small graphs for nu=4, tau>=9.
    """
    print("\n" + "=" * 60)
    print("EXHAUSTIVE SEARCH ON SMALL GRAPHS")
    print("=" * 60)

    # Search graphs on n vertices
    for n in range(6, 11):
        print(f"\nSearching graphs on {n} vertices...")

        # All possible edges
        all_edges = list(itertools.combinations(range(n), 2))
        total_edge_sets = 2 ** len(all_edges)

        # Too many to enumerate directly, sample randomly
        import random
        random.seed(42)

        samples = min(10000, total_edge_sets)
        found_counterexample = False

        for _ in range(samples):
            # Random edge set
            num_edges = random.randint(n, len(all_edges))
            edge_indices = random.sample(range(len(all_edges)), num_edges)
            edges = {all_edges[i] for i in edge_indices}

            triangles = triangles_in_graph(edges)
            if len(triangles) < 4:
                continue

            nu, _ = compute_nu(triangles)
            if nu != 4:
                continue

            tau = compute_tau(edges, triangles)
            if tau >= 9:
                print(f"\n  *** POTENTIAL COUNTEREXAMPLE! ***")
                print(f"  Vertices: {n}")
                print(f"  Edges: {edges}")
                print(f"  nu = {nu}, tau = {tau}")
                found_counterexample = True
                break

        if found_counterexample:
            break
        else:
            print(f"  No counterexample in {samples} samples")

if __name__ == "__main__":
    analyze_cycle4_with_sunflowers()
    analyze_forced_externals()
    search_constrained_externals()
    search_with_two_apexes()
    find_extreme_configuration()
    exhaustive_small_search()
