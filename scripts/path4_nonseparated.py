#!/usr/bin/env python3
"""
Analyze the "non-separated" case for PATH_4 packings in Tuza's conjecture.

PATH_4 packing M = {A,B,C,D} where:
  A--B--C--D (path of 4 triangles)
  Adjacent pairs share exactly 1 vertex, non-adjacent share ≤1
  All pairs are edge-disjoint

Label: A={v1,a1,a2}, B={v1,v2,b1}, C={v2,v3,c1}, D={v3,d1,d2}

We focus on the case A∩(C∪D) ≠ ∅ ("non-separated").
"""

import itertools
from collections import defaultdict
import time

def edges_of(tri):
    """Return the 3 edges of a triangle as frozensets."""
    a, b, c = tri
    return frozenset([frozenset([a,b]), frozenset([a,c]), frozenset([b,c])])

def edges_of_tuple(tri):
    """Return edges as a set of frozensets."""
    a, b, c = tri
    return {frozenset([a,b]), frozenset([a,c]), frozenset([b,c])}

def share_edge(t1, t2):
    return bool(edges_of_tuple(t1) & edges_of_tuple(t2))

def all_triangles_in_graph(graph_edges, n):
    """Find all triangles in the given edge set."""
    adj = defaultdict(set)
    for e in graph_edges:
        u, v = e
        adj[u].add(v)
        adj[v].add(u)
    triangles = []
    verts = list(range(n))
    for i in range(len(verts)):
        for j in range(i+1, len(verts)):
            if verts[j] not in adj[verts[i]]:
                continue
            for k in range(j+1, len(verts)):
                if verts[k] in adj[verts[i]] and verts[k] in adj[verts[j]]:
                    triangles.append((verts[i], verts[j], verts[k]))
    return triangles

def min_edge_cover_triangles(graph_edges, triangles, max_size=10):
    """
    Find minimum set of edges that hits every triangle.
    Uses ILP-style greedy + brute force for small instances.
    """
    if not triangles:
        return 0
    
    # Convert triangles to edge sets
    tri_edge_sets = [edges_of_tuple(t) for t in triangles]
    
    # Only edges that appear in some triangle matter
    relevant_edges = set()
    for tes in tri_edge_sets:
        relevant_edges |= tes
    relevant_edges = list(relevant_edges)
    
    if len(relevant_edges) > 25:
        # Use greedy approximation
        return _greedy_cover(relevant_edges, tri_edge_sets)
    
    # Brute force for small cases
    for size in range(1, min(max_size + 1, len(relevant_edges) + 1)):
        for cover in itertools.combinations(range(len(relevant_edges)), size):
            cover_set = {relevant_edges[i] for i in cover}
            if all(tes & cover_set for tes in tri_edge_sets):
                return size
    return max_size + 1

def _greedy_cover(edges, tri_edge_sets):
    """Greedy triangle cover."""
    uncovered = list(range(len(tri_edge_sets)))
    cover = []
    while uncovered:
        # Pick edge covering most uncovered triangles
        best_edge = None
        best_count = 0
        for e in edges:
            count = sum(1 for i in uncovered if e in tri_edge_sets[i])
            if count > best_count:
                best_count = count
                best_edge = e
        if best_edge is None or best_count == 0:
            break
        cover.append(best_edge)
        uncovered = [i for i in uncovered if best_edge not in tri_edge_sets[i]]
    return len(cover)

def max_packing(triangles, max_search=5):
    """Find maximum edge-disjoint triangle packing."""
    # Sort by number of shared edges (least connected first) for better pruning
    tri_list = list(triangles)
    
    def _search(remaining, current_edges, current_size):
        best = current_size
        for i, t in enumerate(remaining):
            te = edges_of_tuple(t)
            if te & current_edges:
                continue
            new_best = _search(remaining[i+1:], current_edges | te, current_size + 1)
            best = max(best, new_best)
            if best >= max_search:
                return best
        return best
    
    return _search(tri_list, set(), 0)


def enumerate_path4_packings(n, only_nonseparated=True):
    """
    Enumerate PATH_4 packings on Fin n.
    Returns list of (A, B, C, D, info_dict).
    
    Optimized: build adjacency structures first.
    """
    vertices = list(range(n))
    all_tris = list(itertools.combinations(vertices, 3))
    
    # Pre-compute edges for each triangle
    tri_edges = {t: edges_of_tuple(t) for t in all_tris}
    
    # Build index: for each vertex, which triangles contain it
    vert_to_tris = defaultdict(list)
    for t in all_tris:
        for v in t:
            vert_to_tris[v].append(t)
    
    # Build index: for each pair of vertices, which triangles contain both
    pair_to_tris = defaultdict(list)
    for t in all_tris:
        for i in range(3):
            for j in range(i+1, 3):
                pair_to_tris[frozenset([t[i], t[j]])].append(t)
    
    packings = []
    
    for A in all_tris:
        a_edges = tri_edges[A]
        a_set = set(A)
        
        # B must share exactly 1 vertex with A (call it v1), no shared edge
        for v1 in A:
            # B contains v1 and two other vertices, no shared edge with A
            for B in vert_to_tris[v1]:
                if B <= A:  # avoid some duplicates? Actually no, order matters in path
                    pass  # We need ordered paths, don't skip
                b_set = set(B)
                if len(a_set & b_set) != 1:
                    continue
                if a_edges & tri_edges[B]:
                    continue
                
                v2_candidates = b_set - {v1}
                
                for v2 in v2_candidates:
                    b1 = (b_set - {v1, v2}).pop()
                    
                    # C must share exactly v2 with B, share ≤1 with A, no shared edges with A or B
                    for C in vert_to_tris[v2]:
                        c_set = set(C)
                        if len(b_set & c_set) != 1:
                            continue
                        if len(a_set & c_set) > 1:
                            continue
                        if tri_edges[B] & tri_edges[C]:
                            continue
                        if a_edges & tri_edges[C]:
                            continue
                        
                        v3_candidates = c_set - {v2}
                        
                        for v3 in v3_candidates:
                            c1 = (c_set - {v2, v3}).pop()
                            
                            # D must share exactly v3 with C, share ≤1 with A and B, 
                            # no shared edges with A, B, or C
                            for D in vert_to_tris[v3]:
                                d_set = set(D)
                                if len(c_set & d_set) != 1:
                                    continue
                                if len(a_set & d_set) > 1:
                                    continue
                                if len(b_set & d_set) > 1:
                                    continue
                                if tri_edges[C] & tri_edges[D]:
                                    continue
                                if tri_edges[B] & tri_edges[D]:
                                    continue
                                if a_edges & tri_edges[D]:
                                    continue
                                
                                # Valid PATH_4: A--B--C--D
                                # Shared vertices: v1=A∩B, v2=B∩C, v3=C∩D
                                
                                ac_shared = a_set & c_set
                                ad_shared = a_set & d_set
                                bd_shared = b_set & d_set
                                
                                a_shares_cd = bool(ac_shared) or bool(ad_shared)
                                
                                if only_nonseparated and not a_shares_cd:
                                    continue
                                
                                # Classify vertices
                                a1, a2 = sorted(a_set - {v1})
                                d1, d2 = sorted(d_set - {v3})
                                
                                all_verts = a_set | b_set | c_set | d_set
                                n_distinct = len(all_verts)
                                
                                info = {
                                    'v1': v1, 'v2': v2, 'v3': v3,
                                    'a1': a1, 'a2': a2, 'b1': b1, 'c1': c1,
                                    'd1': d1, 'd2': d2,
                                    'ac_shared': ac_shared,
                                    'ad_shared': ad_shared,
                                    'bd_shared': bd_shared,
                                    'n_distinct': n_distinct,
                                    'all_verts': all_verts,
                                }
                                
                                packings.append((A, B, C, D, info))
    
    return packings


def classify_sharing(info):
    """Classify the sharing pattern abstractly."""
    patterns = []
    
    v1, v2, v3 = info['v1'], info['v2'], info['v3']
    a1, a2, b1, c1 = info['a1'], info['a2'], info['b1'], info['c1']
    d1, d2 = info['d1'], info['d2']
    
    for w in info['ac_shared']:
        # w is in A and C. w != v1 (since v1 not in C unless v1=v2 which can't happen)
        # Actually w could be v2 if v2 in A, but v2 is in B and |A∩B|=1 means v2 not in A unless v2=v1
        # So w is a1 or a2
        a_role = 'a1' if w == a1 else 'a2'
        # In C: w is v2, v3, or c1
        if w == v2:
            c_role = 'v2'
        elif w == v3:
            c_role = 'v3'
        else:
            c_role = 'c1'
        patterns.append(f"A∩C:{a_role}={c_role}")
    
    for w in info['ad_shared']:
        a_role = 'v1' if w == v1 else ('a1' if w == a1 else 'a2')
        if w == v3:
            d_role = 'v3'
        elif w == d1:
            d_role = 'd1'
        else:
            d_role = 'd2'
        patterns.append(f"A∩D:{a_role}={d_role}")
    
    for w in info['bd_shared']:
        if w == v1:
            b_role = 'v1'
        elif w == v2:
            b_role = 'v2'
        else:
            b_role = 'b1'
        if w == v3:
            d_role = 'v3'
        elif w == d1:
            d_role = 'd1'
        else:
            d_role = 'd2'
        patterns.append(f"B∩D:{b_role}={d_role}")
    
    return tuple(sorted(patterns))


def analyze_worst_case_tau(A, B, C, D, info, n):
    """
    For the given packing, construct the worst-case graph and compute tau.
    
    Start with the 4 packing triangles.
    Add all edges among the packing vertices to form the complete graph on those vertices.
    Find all triangles, compute nu and tau.
    """
    all_verts = info['all_verts']
    
    # Complete graph on packing vertices
    complete_edges = set()
    vlist = sorted(all_verts)
    for i in range(len(vlist)):
        for j in range(i+1, len(vlist)):
            complete_edges.add(frozenset([vlist[i], vlist[j]]))
    
    # Find all triangles in complete graph
    all_triangles = all_triangles_in_graph(complete_edges, n)
    
    # Compute nu (max packing)
    nu = max_packing(all_triangles, max_search=6)
    
    # Compute tau (min cover)
    tau = min_edge_cover_triangles(complete_edges, all_triangles, max_size=12)
    
    return nu, tau, len(all_triangles)


def analyze_constrained_tau(A, B, C, D, info, n):
    """
    For the given PATH_4 packing, find the graph G where:
    - G contains all edges of A, B, C, D
    - nu(G) = 4 (exactly, not more)
    - tau(G) is maximized
    
    Strategy: start with complete graph on packing vertices,
    remove edges to get nu=4, while keeping tau high.
    
    Actually, let's just compute tau for the complete graph on packing verts
    and check if nu ≤ 4 (if so, tau is the answer; if nu > 4, we'd need to 
    remove edges, which only decreases tau).
    """
    all_verts = sorted(info['all_verts'])
    nv = len(all_verts)
    
    # Complete graph on packing vertices
    complete_edges = set()
    for i in range(nv):
        for j in range(i+1, nv):
            complete_edges.add(frozenset([all_verts[i], all_verts[j]]))
    
    # Packing edges (must be in G)
    packing_edges = edges_of_tuple(A) | edges_of_tuple(B) | edges_of_tuple(C) | edges_of_tuple(D)
    
    # All triangles in complete graph
    all_triangles = all_triangles_in_graph(complete_edges, n)
    
    # Check nu of complete graph
    nu_complete = max_packing(all_triangles, max_search=6)
    tau_complete = min_edge_cover_triangles(complete_edges, all_triangles, max_size=12)
    
    return {
        'n_verts': nv,
        'nu_complete': nu_complete,
        'tau_complete': tau_complete,
        'n_triangles_complete': len(all_triangles),
    }


def main():
    start = time.time()
    
    for n in [8, 9]:
        print(f"\n{'='*70}")
        print(f"  Fin {n}: Enumerating non-separated PATH_4 packings")
        print(f"{'='*70}")
        
        t0 = time.time()
        packings = enumerate_path4_packings(n, only_nonseparated=True)
        t1 = time.time()
        print(f"\nFound {len(packings)} non-separated PATH_4 packings in {t1-t0:.1f}s")
        
        if not packings:
            print("No non-separated packings found.")
            continue
        
        # Classify by sharing pattern
        pattern_counts = defaultdict(int)
        pattern_examples = {}
        pattern_nvert_range = defaultdict(lambda: [100, 0])
        
        for A, B, C, D, info in packings:
            pat = classify_sharing(info)
            pattern_counts[pat] += 1
            nv = info['n_distinct']
            r = pattern_nvert_range[pat]
            r[0] = min(r[0], nv)
            r[1] = max(r[1], nv)
            if pat not in pattern_examples:
                pattern_examples[pat] = (A, B, C, D, info)
        
        print(f"\n--- Sharing Pattern Classification ---")
        print(f"{'Pattern':<50} {'Count':>7} {'#Verts':>10}")
        print("-" * 70)
        for pat in sorted(pattern_counts.keys(), key=lambda p: -pattern_counts[p]):
            cnt = pattern_counts[pat]
            lo, hi = pattern_nvert_range[pat]
            vrange = f"{lo}" if lo == hi else f"{lo}-{hi}"
            print(f"{str(pat):<50} {cnt:>7} {vrange:>10}")
        
        # Detailed analysis of each pattern
        print(f"\n--- Detailed Analysis per Pattern ---")
        for pat in sorted(pattern_counts.keys(), key=lambda p: -pattern_counts[p]):
            A, B, C, D, info = pattern_examples[pat]
            print(f"\nPattern: {pat}")
            print(f"  Example: A={A}, B={B}, C={C}, D={D}")
            print(f"  Spine: v1={info['v1']}, v2={info['v2']}, v3={info['v3']}")
            print(f"  Free: a1={info['a1']}, a2={info['a2']}, b1={info['b1']}, c1={info['c1']}, d1={info['d1']}, d2={info['d2']}")
            print(f"  Distinct vertices: {info['n_distinct']}, Vertices: {sorted(info['all_verts'])}")
            
            # Analyze tau for this example
            result = analyze_constrained_tau(A, B, C, D, info, n)
            print(f"  Complete graph on packing verts:")
            print(f"    nu={result['nu_complete']}, tau={result['tau_complete']}, #triangles={result['n_triangles_complete']}")
        
        # Key question: are there patterns where the complete graph has nu=4?
        print(f"\n--- Searching for packings where complete(packing_verts) has nu=4 ---")
        nu4_count = 0
        nu4_max_tau = 0
        nu4_examples = []
        
        # Sample if too many packings
        sample = packings if len(packings) <= 500 else packings[::len(packings)//500 + 1]
        
        for A, B, C, D, info in sample:
            result = analyze_constrained_tau(A, B, C, D, info, n)
            if result['nu_complete'] == 4:
                nu4_count += 1
                if result['tau_complete'] > nu4_max_tau:
                    nu4_max_tau = result['tau_complete']
                if result['tau_complete'] >= 7:
                    nu4_examples.append((A, B, C, D, info, result))
        
        print(f"  Checked {len(sample)} packings")
        print(f"  nu=4 on complete graph: {nu4_count}")
        print(f"  Max tau among nu=4 cases: {nu4_max_tau}")
        
        if nu4_examples:
            print(f"\n  Examples with nu=4 and tau >= 7:")
            for A, B, C, D, info, result in nu4_examples[:5]:
                pat = classify_sharing(info)
                print(f"    A={A}, B={B}, C={C}, D={D}")
                print(f"    Pattern: {pat}, #verts={info['n_distinct']}")
                print(f"    nu={result['nu_complete']}, tau={result['tau_complete']}")
        
        # Specifically check: when both A∩(C∪D)≠∅ AND D∩(A∪B)≠∅
        print(f"\n--- Both-endpoint sharing: A∩(C∪D)≠∅ AND D∩(A∪B)≠∅ ---")
        both_count = 0
        both_patterns = defaultdict(int)
        both_nvert = defaultdict(int)
        
        for A, B, C, D, info in packings:
            a_shares = bool(info['ac_shared']) or bool(info['ad_shared'])
            d_shares = bool(info['ad_shared']) or bool(info['bd_shared'])
            if a_shares and d_shares:
                both_count += 1
                pat = classify_sharing(info)
                both_patterns[pat] += 1
                both_nvert[info['n_distinct']] += 1
        
        print(f"  Total: {both_count}")
        print(f"  By vertex count: {dict(sorted(both_nvert.items()))}")
        print(f"  Patterns:")
        for pat, cnt in sorted(both_patterns.items(), key=lambda x: -x[1]):
            print(f"    {pat}: {cnt}")
    
    # Special deep analysis on small vertex count cases
    print(f"\n{'='*70}")
    print(f"  DEEP ANALYSIS: Non-separated packings with ≤8 distinct vertices")
    print(f"{'='*70}")
    
    for n in [8, 9]:
        packings = enumerate_path4_packings(n, only_nonseparated=True)
        for A, B, C, D, info in packings:
            if info['n_distinct'] > 8:
                continue
            
            pat = classify_sharing(info)
            all_verts = sorted(info['all_verts'])
            nv = len(all_verts)
            
            # Complete graph analysis
            complete_edges = set()
            for i in range(nv):
                for j in range(i+1, nv):
                    complete_edges.add(frozenset([all_verts[i], all_verts[j]]))
            
            all_triangles = all_triangles_in_graph(complete_edges, n)
            nu_c = max_packing(all_triangles, max_search=6)
            tau_c = min_edge_cover_triangles(complete_edges, all_triangles, max_size=12)
            
            # Now try to find a subgraph with nu=4 and maximum tau
            # Strategy: remove edges not in packing to reduce nu to 4
            packing_edges = edges_of_tuple(A) | edges_of_tuple(B) | edges_of_tuple(C) | edges_of_tuple(D)
            optional_edges = complete_edges - packing_edges
            
            # Try: packing edges only
            packing_tris = all_triangles_in_graph(packing_edges, n)
            nu_pack = max_packing(packing_tris, max_search=5)
            tau_pack = min_edge_cover_triangles(packing_edges, packing_tris, max_size=12)
            
            print(f"\n  Packing: A={A}, B={B}, C={C}, D={D}")
            print(f"  Pattern: {pat}, #verts={nv}")
            print(f"  Complete({nv}): nu={nu_c}, tau={tau_c}, #tri={len(all_triangles)}")
            print(f"  Packing-only: nu={nu_pack}, tau={tau_pack}, #tri={len(packing_tris)}")
            
            # Try adding edges one by one from optional, tracking nu
            # Find the graph with most edges that still has nu=4
            if nu_c > 4 and nv <= 8:
                # Search for max-tau subgraph with nu=4
                # This is expensive; do a greedy approach
                best_tau_nu4 = tau_pack
                current_edges = set(packing_edges)
                opt_list = list(optional_edges)
                
                for e in opt_list:
                    test_edges = current_edges | {e}
                    test_tris = all_triangles_in_graph(test_edges, n)
                    test_nu = max_packing(test_tris, max_search=5)
                    if test_nu <= 4:
                        current_edges = test_edges
                        test_tau = min_edge_cover_triangles(test_edges, test_tris, max_size=12)
                        best_tau_nu4 = max(best_tau_nu4, test_tau)
                
                final_tris = all_triangles_in_graph(current_edges, n)
                final_nu = max_packing(final_tris, max_search=5)
                final_tau = min_edge_cover_triangles(current_edges, final_tris, max_size=12)
                print(f"  Max-edges nu=4 subgraph: nu={final_nu}, tau={final_tau}, #edges={len(current_edges)}, #tri={len(final_tris)}")
    
    elapsed = time.time() - start
    print(f"\n\nTotal runtime: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
