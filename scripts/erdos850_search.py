#!/usr/bin/env python3
"""
Erdős Problem 850: Search for distinct x, y such that
  primeFactors(x) = primeFactors(y)
  primeFactors(x+1) = primeFactors(y+1)
  primeFactors(x+2) = primeFactors(y+2)

where primeFactors(n) is the set of prime divisors of n.

Strategy: sieve-based factorization for speed, then group by triples.
"""

import time
from collections import defaultdict

def sieve_prime_factor_sets(N):
    """
    Compute the set of prime factors for every integer from 0 to N
    using a sieve approach. Returns a list where pf[n] = frozenset of prime factors of n.
    """
    # Initialize: each number starts with an empty set
    pf = [set() for _ in range(N + 1)]
    
    for p in range(2, N + 1):
        if not pf[p]:  # p is prime (no prime factors added yet)
            for m in range(p, N + 1, p):
                pf[m].add(p)
    
    # Convert to frozensets for hashing
    return [frozenset(s) for s in pf]


def main():
    N = 100_000
    print(f"Erdős Problem 850: Searching for solutions up to N = {N:,}")
    print("=" * 70)
    
    # Phase 1: Sieve factorization
    t0 = time.time()
    pf = sieve_prime_factor_sets(N + 2)  # Need up to N+2 for x+2 when x=N
    t1 = time.time()
    print(f"\nSieve completed in {t1 - t0:.2f}s")
    
    # Phase 2: Search for triple matches (the full Erdős 850 problem)
    print(f"\n{'='*70}")
    print("PHASE 2: Triple matching — primeFactors for (x, x+1, x+2)")
    print(f"{'='*70}")
    
    triple_groups = defaultdict(list)
    for x in range(2, N + 1):
        triple = (pf[x], pf[x + 1], pf[x + 2])
        triple_groups[triple].append(x)
    
    solutions_found = []
    for triple, xs in triple_groups.items():
        if len(xs) >= 2:
            solutions_found.append((triple, xs))
    
    if solutions_found:
        print(f"\n*** SOLUTIONS FOUND: {len(solutions_found)} triple groups with 2+ values ***\n")
        for triple, xs in sorted(solutions_found, key=lambda t: t[1][0])[:20]:
            pf_strs = ['{' + ','.join(str(p) for p in sorted(s)) + '}' for s in triple]
            print(f"  Triple: ({pf_strs[0]}, {pf_strs[1]}, {pf_strs[2]})")
            print(f"  x values: {xs[:10]}{'...' if len(xs) > 10 else ''}")
            for i in range(min(len(xs), 5)):
                for j in range(i + 1, min(len(xs), 5)):
                    x_val, y_val = xs[i], xs[j]
                    print(f"    Solution pair: (x={x_val}, y={y_val})")
                    for k in range(3):
                        n1, n2 = x_val + k, y_val + k
                        print(f"      pf({n1}) = {set(sorted(pf[n1]))} = pf({n2}) = {set(sorted(pf[n2]))}")
            print()
    else:
        print(f"\n  No solutions found for x < {N:,}")
    
    # Phase 3: Statistics on pair matching (2 consecutive)
    print(f"\n{'='*70}")
    print("PHASE 3: Pair matching — primeFactors for (x, x+1)")
    print(f"{'='*70}")
    
    pair_groups = defaultdict(list)
    for x in range(2, N + 1):
        pair = (pf[x], pf[x + 1])
        pair_groups[pair].append(x)
    
    num_distinct_pairs = len(pair_groups)
    pair_matches = {pair: xs for pair, xs in pair_groups.items() if len(xs) >= 2}
    num_pair_matches = len(pair_matches)
    
    max_pair_group = max(pair_groups.items(), key=lambda t: len(t[1]))
    
    print(f"\n  Total distinct (pf(x), pf(x+1)) pairs: {num_distinct_pairs:,}")
    print(f"  Pairs with 2+ matching x values: {num_pair_matches:,}")
    print(f"  Fraction with matches: {num_pair_matches / num_distinct_pairs:.4f}")
    print(f"  Maximum group size: {len(max_pair_group[1])}")
    
    pair_key = max_pair_group[0]
    pf_strs = ['{' + ','.join(str(p) for p in sorted(s)) + '}' for s in pair_key]
    print(f"    Pair: ({pf_strs[0]}, {pf_strs[1]})")
    print(f"    x values (first 20): {max_pair_group[1][:20]}")
    
    print(f"\n  Top 10 largest pair groups:")
    sorted_pairs = sorted(pair_groups.items(), key=lambda t: -len(t[1]))
    for i, (pair_key, xs) in enumerate(sorted_pairs[:10]):
        pf_strs = ['{' + ','.join(str(p) for p in sorted(s)) + '}' for s in pair_key]
        print(f"    #{i+1}: size {len(xs):>4} | ({pf_strs[0]}, {pf_strs[1]}) | first: {xs[:5]}")
    
    # Phase 4: Near-misses for triples (match 2 out of 3)
    print(f"\n{'='*70}")
    print("PHASE 4: Near-misses — matching 2 out of 3 in triple")
    print(f"{'='*70}")
    
    near_miss_01 = 0  # match on positions 0,1 but not 2
    near_miss_12 = 0  # match on positions 1,2 but not 0
    near_miss_02 = 0  # match on positions 0,2 but not 1
    
    # Near-misses from pair matches on (x, x+1) — positions 0,1
    for pair_key, xs in pair_groups.items():
        if len(xs) >= 2:
            pf2_values = set(pf[x + 2] for x in xs)
            if len(pf2_values) > 1:
                near_miss_01 += 1
    
    # Check pair matches on (x+1, x+2) — positions 1,2
    pair12_groups = defaultdict(list)
    for x in range(2, N + 1):
        pair12 = (pf[x + 1], pf[x + 2])
        pair12_groups[pair12].append(x)
    
    for pair_key, xs in pair12_groups.items():
        if len(xs) >= 2:
            pf0_values = set(pf[x] for x in xs)
            if len(pf0_values) > 1:
                near_miss_12 += 1
    
    # Check pair matches on (x, x+2) — positions 0,2
    pair02_groups = defaultdict(list)
    for x in range(2, N + 1):
        pair02 = (pf[x], pf[x + 2])
        pair02_groups[pair02].append(x)
    
    for pair_key, xs in pair02_groups.items():
        if len(xs) >= 2:
            pf1_values = set(pf[x + 1] for x in xs)
            if len(pf1_values) > 1:
                near_miss_02 += 1
    
    print(f"\n  Groups matching positions (0,1) but split on (2): {near_miss_01}")
    print(f"  Groups matching positions (0,2) but split on (1): {near_miss_02}")
    print(f"  Groups matching positions (1,2) but split on (0): {near_miss_12}")
    
    # Phase 5: Show some concrete near-misses
    print(f"\n{'='*70}")
    print("PHASE 5: Concrete near-miss examples (matching 2 of 3, pf(x+2) differs by ≤1 prime)")
    print(f"{'='*70}")
    
    near_examples = []
    for pair_key, xs in pair_groups.items():
        if len(xs) >= 2:
            for i in range(min(len(xs), 10)):
                for j in range(i + 1, min(len(xs), 10)):
                    x1, x2 = xs[i], xs[j]
                    s1, s2 = pf[x1 + 2], pf[x2 + 2]
                    sym_diff = s1.symmetric_difference(s2)
                    if len(sym_diff) <= 2:  # Close match
                        near_examples.append((len(sym_diff), x1, x2, s1, s2))
    
    near_examples.sort()
    print(f"\n  Found {len(near_examples)} near-misses where pf(x+2) differs by ≤1 prime")
    for diff_size, x1, x2, s1, s2 in near_examples[:15]:
        print(f"    x={x1}, y={x2}: pf match on (x,x+1), "
              f"pf(x+2)={set(sorted(s1))}, pf(y+2)={set(sorted(s2))}, "
              f"sym_diff={set(sorted(s1.symmetric_difference(s2)))}")
    
    # Phase 6: Triple statistics
    print(f"\n{'='*70}")
    print("PHASE 6: Triple statistics")
    print(f"{'='*70}")
    
    num_distinct_triples = len(triple_groups)
    triple_matches = sum(1 for xs in triple_groups.values() if len(xs) >= 2)
    max_triple = max(triple_groups.items(), key=lambda t: len(t[1]))
    
    print(f"\n  Total distinct (pf(x), pf(x+1), pf(x+2)) triples: {num_distinct_triples:,}")
    print(f"  Triples with 2+ matching x values: {triple_matches:,}")
    print(f"  Maximum triple group size: {len(max_triple[1])}")
    
    triple_key = max_triple[0]
    pf_strs = ['{' + ','.join(str(p) for p in sorted(s)) + '}' for s in triple_key]
    print(f"    Triple: ({pf_strs[0]}, {pf_strs[1]}, {pf_strs[2]})")
    print(f"    x values: {max_triple[1][:20]}")
    
    # Distribution of triple group sizes
    size_dist = defaultdict(int)
    for xs in triple_groups.values():
        size_dist[len(xs)] += 1
    
    print(f"\n  Triple group size distribution:")
    for size in sorted(size_dist.keys()):
        print(f"    Size {size}: {size_dist[size]:,} groups")
    
    t2 = time.time()
    print(f"\n{'='*70}")
    print(f"Total runtime: {t2 - t0:.2f}s")
    print(f"{'='*70}")
    
    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    if solutions_found:
        print(f"\n  *** {len(solutions_found)} SOLUTIONS FOUND for Erdős 850 with x < {N:,} ***")
        total_pairs = sum(len(xs) * (len(xs) - 1) // 2 for _, xs in solutions_found)
        print(f"  Total solution pairs: {total_pairs}")
    else:
        print(f"\n  No solutions to Erdős 850 found for x < {N:,}")
        print(f"  This is consistent with the problem being OPEN.")
        print(f"  The rarity of triple matches suggests solutions may require very large x,")
        print(f"  or may not exist at all.")
    
    print(f"\n  Pair matching (2 consecutive): {num_pair_matches:,} distinct pair-patterns have matches")
    print(f"  Triple matching (3 consecutive): {triple_matches} distinct triple-patterns have matches")


if __name__ == "__main__":
    main()
