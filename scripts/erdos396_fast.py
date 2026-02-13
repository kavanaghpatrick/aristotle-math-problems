"""
Erdos Problem 396: For each k, find smallest n >= k+1 such that
    n*(n-1)*...*(n-k) | C(2n,n)

OPTIMIZED VERSION: Instead of computing C(2n,n) directly (which has millions of digits),
we check divisibility using p-adic valuations:

    v_p(C(2n,n)) = sum_{i>=1} (floor(2n/p^i) - 2*floor(n/p^i))  [Kummer's theorem]
    v_p(n*(n-1)*...*(n-k)) = sum_{j=0}^{k} v_p(n-j)

We need v_p(C(2n,n)) >= v_p(n*(n-1)*...*(n-k)) for all primes p.

Known values (OEIS A375077):
    k=0: n=1, k=1: n=2, k=2: n=2480, k=3: n=8178, k=4: n=45153,
    k=5: n=3648841, k=6: n=7979090, k=7: n=101130029
    k=8: UNKNOWN — this is our target!
"""
import sys
from math import isqrt

def get_primes_up_to(limit):
    """Sieve of Eratosthenes"""
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    return [i for i in range(2, limit + 1) if sieve[i]]

def v_p(n, p):
    """p-adic valuation of n"""
    if n == 0:
        return float('inf')
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def v_p_central_binom(n, p):
    """v_p(C(2n,n)) using Kummer's theorem / Legendre's formula"""
    # v_p(C(2n,n)) = v_p((2n)!) - 2*v_p(n!)
    # = sum_{i>=1} (floor(2n/p^i) - 2*floor(n/p^i))
    # Each term is 0 or 1 (carry in base-p addition of n+n)
    total = 0
    pk = p
    while pk <= 2 * n:
        total += (2 * n) // pk - 2 * (n // pk)
        pk *= p
    return total

def v_p_desc_factorial(n, k, p):
    """v_p(n*(n-1)*...*(n-k))"""
    total = 0
    for j in range(k + 1):
        total += v_p(n - j, p)
    return total

def check_divisibility(n, k, primes_cache):
    """Check if n*(n-1)*...*(n-k) | C(2n,n) using p-adic valuations"""
    # Get all prime factors of n*(n-1)*...*(n-k)
    # We only need primes up to n (since all factors are <= n)
    for p in primes_cache:
        if p > n:
            break
        # Quick check: does p divide any of n, n-1, ..., n-k?
        divides_any = False
        for j in range(k + 1):
            if (n - j) % p == 0:
                divides_any = True
                break
        if not divides_any:
            continue

        vp_desc = v_p_desc_factorial(n, k, p)
        if vp_desc == 0:
            continue
        vp_cb = v_p_central_binom(n, p)
        if vp_cb < vp_desc:
            return False
    return True

def search_erdos396(max_k=10, max_n=10_000_000):
    print(f"Erdos 396 (FAST): searching for witnesses")
    print(f"Max k={max_k}, max n={max_n:,}")

    # Pre-compute primes up to max_n
    prime_limit = min(max_n, 10_000_000)  # cap for memory
    print(f"Sieving primes up to {prime_limit:,}...")
    primes = get_primes_up_to(prime_limit)
    print(f"Found {len(primes):,} primes")

    print(f"\n{'k':>4} {'smallest n':>12}")
    print("-" * 20)

    known = {0: 1, 1: 2, 2: 2480, 3: 8178, 4: 45153, 5: 3648841, 6: 7979090, 7: 101130029}

    results = {}
    for k in range(max_k + 1):
        found = False
        # Skip known values, just verify them
        if k in known and known[k] <= max_n:
            n = known[k]
            ok = check_divisibility(n, k, primes)
            if ok:
                results[k] = n
                print(f"{k:>4} {n:>12} (verified known value)")
                continue
            else:
                print(f"{k:>4} {n:>12} VERIFICATION FAILED!")
                # Fall through to search

        start_n = k + 1
        if k in known:
            start_n = known[k] + 1  # search beyond known value

        for n in range(start_n, max_n + 1):
            if check_divisibility(n, k, primes):
                results[k] = n
                status = "NEW!" if k not in known else "confirmed"
                print(f"{k:>4} {n:>12} ({status})")
                found = True
                break

            if n % 1000000 == 0:
                print(f"  k={k}: searched to n={n:,}...", flush=True)

        if not found:
            print(f"{k:>4} NOT FOUND (searched to {max_n:,})")

    return results

if __name__ == "__main__":
    max_k = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    max_n = int(sys.argv[2]) if len(sys.argv) > 2 else 10_000_000
    search_erdos396(max_k, max_n)
