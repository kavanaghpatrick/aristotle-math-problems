"""
MEGA-7 Round 1: enumerate Pell families x^2 - D*y^2 = c with D <= 1000, |c| <= 100
that admit solutions where x and D*y^2 are both POWERFUL, and produce 3-APs.

Strategy:
- A powerful number n satisfies: for every prime p|n, p^2|n.
- A consecutive powerful 3-AP is (n_k, n_{k+1}, n_{k+2}) with constant gap d.
- We look for Pell families that produce powerful 3-APs in some natural way.

van Doorn's family is x^2 - 7^3 * y^2 = 2, giving triples of form
((x-1)^2, x^2 - 1 = (x-1)(x+1), (x+1)^2) — but x^2-1 isn't always powerful.
Actually van Doorn's family is more subtle: it produces ((x-2)^2, (x-1)^2 * something, 7^3 * y^2)
where the structure forces powerful endpoints.

Generalize: we seek Pell families x^2 - D*y^2 = c such that
- x is "powerful-friendly" (x^2 is automatic; we want x^2 ± δ powerful)
- D*y^2 is powerful when rad(D) | y (so D itself must be cubefree and squareful
  in the sense that D = b^3 * sqfree(D) gives powerful structure)

The MEGA-7 angle: classify ALL such Pell families.
"""

import math
from math import gcd, isqrt

def is_powerful(n: int) -> bool:
    """n is powerful iff every prime in n appears to power >= 2."""
    if n < 1: return False
    if n == 1: return True
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if e < 2:
                return False
        p += 1
    return m == 1  # remaining factor would be a single prime to power 1

def rad(n: int) -> int:
    """Squarefree kernel."""
    if n <= 1: return 1
    r = 1
    p = 2
    m = n
    while p * p <= m:
        if m % p == 0:
            r *= p
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        r *= m
    return r

def factor(n: int) -> dict:
    """Prime factorization."""
    if n <= 1: return {}
    f = {}
    m = n
    p = 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def is_square(n: int) -> bool:
    if n < 0: return False
    r = isqrt(n)
    return r * r == n

def powerful_sieve(N: int) -> list:
    """All powerful numbers up to N."""
    out = []
    # Powerful = a^2 * b^3 with rad(b) | a (Golomb). Equivalently every prime in factorization
    # has exponent >= 2.
    # Direct: write n = m^2 * sqfree(?), it's easier to use Golomb.
    powerful = set([1])
    # a^2 * b^3 for b cubefree-like... actually let's just iterate.
    b = 1
    while b * b * b <= N:
        a = 1
        while (a * a) * (b * b * b) <= N:
            n = (a * a) * (b * b * b)
            if is_powerful(n):
                powerful.add(n)
            a += 1
        b += 1
    return sorted(powerful)


# Step 1: Powerful sieve up to 10^8 (we want triples with values reasonable)
print("Building powerful sieve up to 10^8...")
N_BOUND = 10**8
powerful = powerful_sieve(N_BOUND)
print(f"  Found {len(powerful)} powerful numbers <= {N_BOUND}")

powerful_set = set(powerful)

# Find all consecutive powerful 3-APs up to N_BOUND
print("\nSearching for consecutive powerful 3-APs up to 10^8...")
consec_3aps = []
for i in range(len(powerful) - 2):
    n0, n1, n2 = powerful[i], powerful[i+1], powerful[i+2]
    if 2 * n1 == n0 + n2:
        consec_3aps.append((n0, n1, n2))

print(f"  Found {len(consec_3aps)} consecutive powerful 3-APs up to {N_BOUND}:")
for ap in consec_3aps:
    n0, n1, n2 = ap
    d = n1 - n0
    print(f"    ({n0}, {n1}, {n2})  d={d}")
    print(f"      Factorizations: {factor(n0)}, {factor(n1)}, {factor(n2)}")
