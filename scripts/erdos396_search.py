"""
Erdos Problem 396: For each k, find n such that n*(n-1)*...*(n-k) | C(2n,n)

descFactorial(n, k+1) = n * (n-1) * ... * (n-k)
centralBinom(n) = C(2n, n)

We search for the smallest n >= k+1 such that descFactorial(n, k+1) divides centralBinom(n).
"""

from math import comb, factorial
import sys

def desc_factorial(n, length):
    """n * (n-1) * ... * (n-length+1)"""
    result = 1
    for i in range(length):
        result *= (n - i)
    return result

def search_erdos396(max_k=30, max_n=10_000_000):
    print(f"Erdos 396: searching for witnesses (max_k={max_k}, max_n={max_n:,})")
    print(f"{'k':>4} {'smallest n':>12} {'descFact(n,k+1)':>30} {'verified':>8}")
    print("-" * 60)

    results = {}
    for k in range(max_k + 1):
        found = False
        for n in range(k + 1, max_n + 1):
            df = desc_factorial(n, k + 1)
            if df == 0:
                continue
            cb = comb(2 * n, n)
            if cb % df == 0:
                results[k] = n
                print(f"{k:>4} {n:>12} {df:>30} {'YES':>8}")
                found = True
                break
        if not found:
            print(f"{k:>4} {'NOT FOUND':>12} {'':>30} {'':>8}  (searched to n={max_n:,})")
            # Once we fail to find one, the higher k values are harder
            # But keep going to see the pattern

    print(f"\nResults: found witnesses for k = 0..{max(results.keys()) if results else 'none'}")
    print(f"Witnesses: {results}")
    return results

if __name__ == "__main__":
    max_k = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    max_n = int(sys.argv[2]) if len(sys.argv) > 2 else 1_000_000
    search_erdos396(max_k, max_n)
