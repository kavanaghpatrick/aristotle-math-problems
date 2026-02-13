"""
Erdos Problem 307: Find two finite sets of primes P, Q such that
    (sum 1/p for p in P) * (sum 1/q for q in Q) = 1

We use exact rational arithmetic to avoid floating point issues.
Strategy: enumerate subsets of primes, compute their reciprocal sums,
then check if any two multiply to exactly 1.
"""

from fractions import Fraction
from itertools import combinations
import sys

def get_primes(limit):
    """Sieve of Eratosthenes"""
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    return [i for i in range(2, limit + 1) if sieve[i]]

def reciprocal_sum(primes_subset):
    """Exact rational sum of 1/p for p in primes_subset"""
    return sum(Fraction(1, p) for p in primes_subset)

def search_erdos307(prime_limit=50, max_subset_size=8):
    primes = get_primes(prime_limit)
    print(f"Erdos 307: searching with primes up to {prime_limit} ({len(primes)} primes)")
    print(f"Max subset size: {max_subset_size}")

    # Precompute all reciprocal sums and store them
    # Key: reciprocal sum (Fraction), Value: list of prime subsets achieving it
    sums_to_sets = {}
    total_subsets = 0

    for size in range(1, min(max_subset_size + 1, len(primes) + 1)):
        count = 0
        for subset in combinations(primes, size):
            s = reciprocal_sum(subset)
            if s not in sums_to_sets:
                sums_to_sets[s] = []
            sums_to_sets[s].append(subset)
            count += 1
            total_subsets += 1

            # Check if there exists a complementary sum = 1/s
            if s > 0:
                target = Fraction(1, 1) / s  # We need another set with this sum
                if target in sums_to_sets:
                    for other_subset in sums_to_sets[target]:
                        # Check P and Q are disjoint (not required by problem, but interesting)
                        P = set(subset)
                        Q = set(other_subset)
                        disjoint = P.isdisjoint(Q)
                        print(f"\n*** SOLUTION FOUND ***")
                        print(f"P = {subset}, sum(1/p) = {s} = {float(s):.10f}")
                        print(f"Q = {other_subset}, sum(1/q) = {target} = {float(target):.10f}")
                        print(f"Product = {s * target} = {float(s * target)}")
                        print(f"Disjoint: {disjoint}")
                        return subset, other_subset

        print(f"  Checked all subsets of size {size}: {count:,} subsets, {len(sums_to_sets):,} distinct sums")

    print(f"\nNo solution found. Checked {total_subsets:,} total subsets, {len(sums_to_sets):,} distinct sums")

    # Print the sums closest to useful values (near 1, or whose reciprocal appears)
    print("\nSums closest to 1:")
    for s, sets in sorted(sums_to_sets.items(), key=lambda x: abs(float(x[0]) - 1))[:10]:
        print(f"  {float(s):.10f} = {s}  achieved by {sets[0]}")

    return None, None

if __name__ == "__main__":
    prime_limit = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    max_size = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    search_erdos307(prime_limit, max_size)
