"""
Erdos Problem 686: Can every integer N >= 2 be written as
    N = prod(m+1,...,m+k) / prod(n+1,...,n+k)
for some k >= 2 and m >= n+k?

Note: prod(a+1,...,a+k) = (a+k)! / a! = descFactorial(a+k, k)

So N = descFactorial(m+k, k) / descFactorial(n+k, k)
     = C(m+k, k) / C(n+k, k)

Strategy: for each N, search over k and n, compute if there exists m
such that N * prod(n+1,...,n+k) = prod(m+1,...,m+k).
"""

from math import comb, prod
import sys

def consecutive_product(start, k):
    """Product of (start+1) * (start+2) * ... * (start+k)"""
    return prod(range(start + 1, start + k + 1))

def search_erdos686_for_N(N, max_k=20, max_n=10000):
    """Find k >= 2, n, m >= n+k such that N = prod(m+1..m+k)/prod(n+1..n+k)"""
    for k in range(2, max_k + 1):
        for n in range(0, max_n + 1):
            numer_needed = N * consecutive_product(n, k)
            # We need prod(m+1,...,m+k) = numer_needed
            # prod(m+1,...,m+k) = (m+k)!/(m)!
            # This is an increasing function of m, and we need m >= n + k
            # Binary search for m
            m_min = n + k
            m_max = numer_needed  # crude upper bound

            # Quick check: is numer_needed achievable?
            val_at_min = consecutive_product(m_min, k)
            if val_at_min > numer_needed:
                continue
            if val_at_min == numer_needed:
                return k, n, m_min

            # Binary search
            lo, hi = m_min, min(m_max, m_min + numer_needed)
            # Better upper bound: m+1 <= numer_needed^(1/k), so m <= numer_needed^(1/k)
            hi = min(hi, int(numer_needed ** (1.0 / k)) + 10)

            while lo <= hi:
                mid = (lo + hi) // 2
                val = consecutive_product(mid, k)
                if val == numer_needed:
                    return k, n, mid
                elif val < numer_needed:
                    lo = mid + 1
                else:
                    hi = mid - 1

    return None

def search_erdos686(max_N=100, max_k=20, max_n=10000):
    print(f"Erdos 686: searching for representations N = prod(m+1..m+k)/prod(n+1..n+k)")
    print(f"{'N':>5} {'k':>4} {'n':>8} {'m':>8} {'verified':>8}")
    print("-" * 40)

    results = {}
    not_found = []

    for N in range(2, max_N + 1):
        result = search_erdos686_for_N(N, max_k, max_n)
        if result:
            k, n, m = result
            # Verify
            num = consecutive_product(m, k)
            den = consecutive_product(n, k)
            verified = (num == N * den) and (m >= n + k) and (k >= 2)
            results[N] = (k, n, m)
            print(f"{N:>5} {k:>4} {n:>8} {m:>8} {'YES' if verified else 'FAIL':>8}")
        else:
            not_found.append(N)
            print(f"{N:>5} {'NOT FOUND':>4}")

    print(f"\nFound: {len(results)}/{max_N - 1} values")
    if not_found:
        print(f"NOT FOUND for N = {not_found}")
    else:
        print(f"ALL N from 2 to {max_N} have representations!")

    return results, not_found

if __name__ == "__main__":
    max_N = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    search_erdos686(max_N)
