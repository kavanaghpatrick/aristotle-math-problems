#!/usr/bin/env python3
"""
Systematic search for 8-edge cover in PATH_4 configuration.

PATH_4 Structure:
- A = {v1, a1, a2} with edges: {v1,a1}, {v1,a2}, {a1,a2}
- B = {v1, v2, b} with edges: {v1,v2}, {v1,b}, {v2,b}
- C = {v2, v3, c} with edges: {v2,v3}, {v2,c}, {v3,c}
- D = {v3, d1, d2} with edges: {v3,d1}, {v3,d2}, {d1,d2}

External types (must share edge with M-element):
- A-externals: share edge from {{v1,a1}, {v1,a2}, {a1,a2}}
- B-externals: share edge from {{v1,v2}, {v1,b}, {v2,b}}
- C-externals: share edge from {{v2,v3}, {v2,c}, {v3,c}}
- D-externals: share edge from {{v3,d1}, {v3,d2}, {d1,d2}}
"""

from itertools import combinations
from typing import Set, Tuple, List

# Define all M-edges
M_edges = {
    # A edges
    ('v1', 'a1'), ('v1', 'a2'), ('a1', 'a2'),
    # B edges
    ('v1', 'v2'), ('v1', 'b'), ('v2', 'b'),
    # C edges
    ('v2', 'v3'), ('v2', 'c'), ('v3', 'c'),
    # D edges
    ('v3', 'd1'), ('v3', 'd2'), ('d1', 'd2')
}

# Normalize edges (smaller vertex first for consistency)
def normalize_edge(e):
    return tuple(sorted(e))

M_edges = {normalize_edge(e) for e in M_edges}

# Define M-element edges
A_edges = {('a1', 'a2'), ('a1', 'v1'), ('a2', 'v1')}
B_edges = {('b', 'v1'), ('b', 'v2'), ('v1', 'v2')}
C_edges = {('c', 'v2'), ('c', 'v3'), ('v2', 'v3')}
D_edges = {('d1', 'd2'), ('d1', 'v3'), ('d2', 'v3')}

def covers_M_element(cover: Set[Tuple[str, str]], M_edges: Set[Tuple[str, str]]) -> bool:
    """Check if cover hits all edges of an M-element."""
    return all(any(e == ce or set(e) & set(ce) for ce in cover) for e in M_edges)

def covers_external_type(cover: Set[Tuple[str, str]], shared_edge: Tuple[str, str]) -> bool:
    """
    Check if cover hits an external triangle type.
    External type is defined by which edge it shares with M-element.
    Any triangle containing shared_edge is covered if we hit shared_edge.
    """
    return shared_edge in cover

def is_valid_cover(cover: Set[Tuple[str, str]]) -> Tuple[bool, str]:
    """Check if cover is valid for PATH_4.

    WAIT: The constraint is that cover must hit all M-edges.
    The external constraint is: any external triangle shares an edge with some M-element,
    so if we cover all edges of all M-elements, we automatically cover all externals.

    BUT: We're being asked to use FEWER edges than all M-edges.
    The question is: can we find a subset of M-edges that still covers all triangles?

    This requires checking: does this edge set cover all triangles in the graph?
    But we don't have the full triangle list!

    Let me reconsider: The cover must hit ALL triangles.
    - M-triangles: A, B, C, D
    - External triangles: must share edge with some M-element

    A cover C is valid if:
    1. Every M-triangle is hit by some edge in C
    2. Every external triangle is hit by some edge in C

    For (1): Need to hit A, B, C, D
    For (2): Any external shares an edge with M-element, so hitting that shared edge covers it

    So the constraint is:
    - Cover hits A (need ≥1 edge from A_edges)
    - Cover hits B (need ≥1 edge from B_edges)
    - Cover hits C (need ≥1 edge from C_edges)
    - Cover hits D (need ≥1 edge from D_edges)
    - Cover hits all external types (need the shared edge for each type)
    """

    # Check all M-elements are hit
    if not any(e in cover for e in A_edges):
        return False, "A not covered"
    if not any(e in cover for e in B_edges):
        return False, "B not covered"
    if not any(e in cover for e in C_edges):
        return False, "C not covered"
    if not any(e in cover for e in D_edges):
        return False, "D not covered"

    # Check each M-element's external types
    # A-externals: for each edge type, we need that edge in cover
    for edge in A_edges:
        if not covers_external_type(cover, edge):
            return False, f"A-external type {edge} not covered"

    # B-externals
    for edge in B_edges:
        if not covers_external_type(cover, edge):
            return False, f"B-external type {edge} not covered"

    # C-externals
    for edge in C_edges:
        if not covers_external_type(cover, edge):
            return False, f"C-external type {edge} not covered"

    # D-externals
    for edge in D_edges:
        if not covers_external_type(cover, edge):
            return False, f"D-external type {edge} not covered"

    return True, "Valid cover"

def analyze_cover_structure(cover: Set[Tuple[str, str]]):
    """Analyze which parts of the structure are covered."""
    print(f"\nCover analysis for {len(cover)} edges:")
    print(f"Edges: {sorted(cover)}")

    # Count by M-element
    a_count = len([e for e in cover if e in A_edges])
    b_count = len([e for e in cover if e in B_edges])
    c_count = len([e for e in cover if e in C_edges])
    d_count = len([e for e in cover if e in D_edges])

    print(f"  A: {a_count} edges, B: {b_count} edges, C: {c_count} edges, D: {d_count} edges")

    # Check external coverage
    print("  External coverage:")
    for name, edges in [('A', A_edges), ('B', B_edges), ('C', C_edges), ('D', D_edges)]:
        covered_types = [e for e in edges if e in cover]
        print(f"    {name}: {len(covered_types)}/{len(edges)} types - {covered_types}")

def search_8_covers():
    """Search for all valid 8-edge covers."""
    print("="*80)
    print("SEARCHING FOR 8-EDGE COVERS IN PATH_4")
    print("="*80)
    print(f"\nTotal M-edges: {len(M_edges)}")
    print(f"M-edges: {sorted(M_edges)}\n")

    valid_covers = []

    # Test all 8-edge subsets
    total_combos = 0
    for cover in combinations(M_edges, 8):
        total_combos += 1
        cover_set = set(cover)
        is_valid, reason = is_valid_cover(cover_set)

        if is_valid:
            valid_covers.append(cover_set)
            print(f"\n✓ FOUND VALID 8-COVER #{len(valid_covers)}:")
            analyze_cover_structure(cover_set)

    print(f"\n{'='*80}")
    print(f"RESULTS: {len(valid_covers)} valid 8-covers found out of {total_combos} combinations")
    print(f"{'='*80}")

    if not valid_covers:
        print("\n❌ NO VALID 8-EDGE COVER EXISTS")
        print("\nTesting if 9 edges work...")
        cover9 = search_n_covers(9)
        if not cover9:
            print("\nTesting if 10 edges work...")
            cover10 = search_n_covers(10)

    return valid_covers

def search_n_covers(n: int):
    """Search for minimum covers of size n."""
    print(f"\nSearching for {n}-edge covers...")

    for cover in combinations(M_edges, n):
        cover_set = set(cover)
        is_valid, reason = is_valid_cover(cover_set)

        if is_valid:
            print(f"\n✓ FOUND VALID {n}-COVER:")
            analyze_cover_structure(cover_set)
            return cover_set

    print(f"❌ No valid {n}-cover found")
    return None

def test_fan_apex_strategy():
    """
    Test the fan apex strategy:
    If all externals of an endpoint share a common apex,
    we can cover with fewer edges.
    """
    print("\n" + "="*80)
    print("TESTING FAN APEX STRATEGY")
    print("="*80)

    # Strategy: Pick 2 edges per M-element that maximize external coverage
    strategies = [
        {
            'name': 'Endpoints prioritize bases + one spoke',
            'cover': {
                # A: base + spoke to a1
                ('a1', 'a2'), ('a1', 'v1'),
                # B: both spokes (v1,v2 is shared)
                ('v1', 'v2'), ('b', 'v1'),
                # C: both spokes (v2,v3 is shared)
                ('v2', 'v3'), ('c', 'v2'),
                # D: base + spoke to d1
                ('d1', 'd2'), ('d1', 'v3')
            }
        },
        {
            'name': 'Symmetric spoke selection',
            'cover': {
                # A: two spokes
                ('a1', 'v1'), ('a2', 'v1'),
                # B: spine + one spoke
                ('v1', 'v2'), ('b', 'v1'),
                # C: spine + one spoke
                ('v2', 'v3'), ('c', 'v2'),
                # D: two spokes
                ('d1', 'v3'), ('d2', 'v3')
            }
        },
        {
            'name': 'All spokes through spine vertices',
            'cover': {
                # A: both spokes through v1
                ('a1', 'v1'), ('a2', 'v1'),
                # B: both spokes through v1
                ('v1', 'v2'), ('b', 'v1'),
                # C: both spokes through v3
                ('v2', 'v3'), ('c', 'v3'),
                # D: both spokes through v3
                ('d1', 'v3'), ('d2', 'v3')
            }
        },
        {
            'name': 'Include all bases',
            'cover': {
                # A: base
                ('a1', 'a2'),
                # B: spine
                ('v1', 'v2'),
                # C: spine
                ('v2', 'v3'),
                # D: base
                ('d1', 'd2'),
                # Plus critical spokes
                ('a1', 'v1'), ('b', 'v1'), ('c', 'v2'), ('d1', 'v3')
            }
        }
    ]

    for strategy in strategies:
        print(f"\nStrategy: {strategy['name']}")
        is_valid, reason = is_valid_cover(strategy['cover'])
        if is_valid:
            print(f"  ✓ VALID! This is an 8-edge cover!")
            analyze_cover_structure(strategy['cover'])
        else:
            print(f"  ✗ Invalid: {reason}")
            analyze_cover_structure(strategy['cover'])

if __name__ == '__main__':
    # First try exhaustive search
    valid_covers = search_8_covers()

    # Then try strategic approaches
    test_fan_apex_strategy()
