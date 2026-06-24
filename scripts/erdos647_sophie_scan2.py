#!/usr/bin/env python3
"""
Erdos 647 Sophie-Germain residue scan, part 2.

Combine witnesses n-3 and n-4.

WITNESS n-3 = 3·p where p = (2q-1)/3.
  τ(n-3) ≥ 6 needed (gives n-3+6 = n+3 > n+2).
  τ(3p) = 2 (if p=3) or 4 (if p prime ≠ 3) or ≥ 6 (if p composite).
  So witness n-3 works iff p = (2q-1)/3 is COMPOSITE.

WITNESS n-4 = 4r where r = (q-1)/2.
  τ(n-4) = τ(4r).
  If r is odd (always, since r = (q-1)/2 and q is odd prime):
    n-4 = 4r = 2² · r.
    If r prime: τ(4r) = 3·2 = 6.  n-4+6 = n+2. NOT strictly > n+2. BAD.
    If r=1: τ(4) = 3, n-4+3 = n-1. BAD (but r=1 means q=3, excluded).
    If r composite (and odd):
       - if r = s² for prime s, τ = 3·3 = 9, n-4+9 = n+5 > n+2. OK
       - if r = s·t with s<t primes: τ = 3·4 = 12. OK
       - in general τ(4r) ≥ 9 when r is composite ≥ 9.
  So witness n-4 works iff r = (q-1)/2 is COMPOSITE and ≥ 9.

Combined: witness EITHER n-3 OR n-4 works UNLESS
  (q-1)/2 is prime AND (2q-1)/3 is prime
  (Cunningham chain of length ≥ 3 starting from r, with q=2r+1, p_next on top).

Actually need to count r = 1 case too (q=3 excluded since q ≥ 1499).

Let's verify: for q ≥ 1499 (Sophie Germain),
  - witness n-3 OR n-4 works iff NOT (r prime AND p prime).
"""

import math
from sympy import isprime


def sieve_primes(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(math.isqrt(n)) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return s


def main():
    BOUND_N = 1000000  # n up to 10^6
    print(f"Scanning Sophie Germain pairs n ∈ [3000, {BOUND_N}], n ≡ 0 mod 6\n")

    sieve = sieve_primes(BOUND_N + 10)

    sophie_pairs = []
    for n in range(3000, BOUND_N + 1, 6):
        if not sieve[n - 1]:
            continue
        q = (n - 2) // 2
        if q >= len(sieve) or not sieve[q]:
            continue
        sophie_pairs.append((n, q))

    total = len(sophie_pairs)
    print(f"Total Sophie pairs: {total}\n")

    # Classify each pair by (n-3 works, n-4 works) combination
    n3_only = 0   # p=(2q-1)/3 composite, r=(q-1)/2 prime
    n4_only = 0   # r composite, p prime
    both = 0      # r composite AND p composite
    neither = 0   # r prime AND p prime  (Cunningham chain length ≥ 3 above q)

    neither_list = []
    for (n, q) in sophie_pairs:
        r = (q - 1) // 2
        p = (2 * q - 1) // 3  # always integer since 6 | n -> 3 | 2q-1
        # witness n-3 works: τ(3p) ≥ 6 i.e. p composite, p > 3 (always for q ≥ 1499)
        n3_works = (p > 3) and (not isprime(p))
        # witness n-4 works: τ(4r) ≥ 9 i.e. r composite (r odd since q odd prime).
        # for r ≥ 9 composite, τ(4r) ≥ 9
        n4_works = (r >= 9) and (not isprime(r))
        if n3_works and n4_works:
            both += 1
        elif n3_works and not n4_works:
            n3_only += 1
        elif not n3_works and n4_works:
            n4_only += 1
        else:
            neither += 1
            neither_list.append((n, q, r, p))

    print(f"Both n-3 and n-4 work: {both} ({both/total*100:.2f}%)")
    print(f"Only n-3 works (r prime): {n3_only} ({n3_only/total*100:.2f}%)")
    print(f"Only n-4 works (p prime): {n4_only} ({n4_only/total*100:.2f}%)")
    print(f"NEITHER works (r prime AND p prime - Cunningham chain): {neither} ({neither/total*100:.2f}%)")
    print()
    print(f"COMBINED COVERAGE (n-3 OR n-4 works): {total - neither} / {total} = {(total-neither)/total*100:.4f}%")
    print()
    print(f"Uncovered Cunningham-chain cases: {neither} ({neither/total*100:.4f}%)")
    print()
    print("All uncovered cases (need separate handling):")
    for (n, q, r, p) in neither_list[:30]:
        chain = f"chain: {r}, {q}, {p}"
        # is 2p+1 also prime?  next link
        extra = " (4-chain)" if isprime(2 * p + 1) else ""
        print(f"  n={n:>9}  q={q:>8}  r={r:>7}  p={p:>7}  ({chain}){extra}")
    if len(neither_list) > 30:
        print(f"  ... and {len(neither_list) - 30} more")


if __name__ == "__main__":
    main()
